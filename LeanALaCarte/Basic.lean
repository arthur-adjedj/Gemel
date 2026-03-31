import LeanALaCarte.Elab
import LeanALaCarte.ModularCommand
open Lean Meta Elab Command Term

partial def modmapAux (map : ModularMap) (e : Expr): MetaM Expr := do
  withIncRecDepth do
  -- withNewMCtxDepth do
  withTraceNode `Modular.Subst (λ exn => return m!"modmapAux {indentExpr e} \n⇒{exn.toOption.map indentExpr}") do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const fnName lvls := fn then -- TODO manage universes better
    -- One might want to, if a constant is not already extended at this point but should be (e.g if its type contains things that have a partial map), delta-reduce the constant and map it as well.
    -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constants topographically to ensure this.
    let ext? := map[fnName.eraseMacroScopes]?
    if let some ext := ext? then
      --If the partial map has more args than given in the term, we need to eta-expand to avoid producing a term with loose bvars.
      unless ext.numArgs <= args.size do
        return ← modmapAux map (← Meta.etaExpand e)
      let newArgs ← modmapArgs args
      let res := ext.translation
        |>.instantiateLevelParams ext.levelParams lvls
        |>.instantiateRev newArgs[:ext.numArgs]
      trace[Modular.Subst] m!"args instantiated : {res}"
      trace[Modular.Subst] m!"numHoles : {ext.numHoles}"
      -- The produced mvars are "synthetic", i.e they ought to be resolved by the users using tactics or other automations rather than through unification. We may want to use some heuristics in some cases to resolve these automatically when possible.
      let mvars ← Array.mkM ext.numHoles (mkFreshExprMVar none .syntheticOpaque)
      trace[Modular.Subst] m!"mvars : {mvars}"
      let res := res.instantiateRev mvars
      trace[Modular.Subst] m!"mvars instantiated : {res}"
      let res := mkAppN res newArgs[ext.numArgs:]
      trace[Modular.Subst] m!"with extra args : {res}"
      if ext.numArgs != 0 then
        check res  --typecheck the result, which should give a sensible type to each synthetic mvar introduced in the term, and throw a type-error if the generated term is ill-formed.
        -- TODO For (much) better performance in the future, rather than `check` every translation that introduces an mvar, it would make a lot more sense to store the information necessary to infer the type of those mvars in the `ModularExtension`s, I just haven't thought hard enough about how to do that well for now
      let res ← instantiateMVars res
      return res
    else
      let newArgs ← modmapArgs args
      return mkAppN fn newArgs
  else
    let newFn ← traverse fn
    let newArgs ← modmapArgs args
    return mkAppN newFn newArgs
where
  modmapArgs args := args.foldlM (init := Array.emptyWithCapacity args.size) fun nargs e => do
    let arg ← modmapAux map e
    return nargs.push arg

  traverse e: MetaM Expr := match e with
    | .sort _
    | .lit _ --What if you extend Nat/String ? you probably want literals to be translated accordingly, but that's an edge-case not worth thinking about for now
    | .bvar _ | .fvar _ | .mvar _ => pure e
    | .proj tyName idx struct => do
      if let some _ext := map[tyName.eraseMacroScopes]? then
        /- Plan here:
           - look into `ext.translation`, make sure its head is a constant that is structureLike (otherwise throw an exception, we cannot produce "projections" for a type that has more than one constructor/is indexed)
           - use the corresponding constant as the new head
           TODO what if the mapping is partial and the type contains holes ? In practice, shouldn't be an issue as said holes would morally be filled as part of the types of the mapped `struct`
        -/
        panic! "todo"
      else
        let newStruct ← modmapAux map struct
        return .proj tyName idx newStruct
    | .letE ..
    | .lam .. =>
      lambdaLetTelescope e fun xs e => withmodmappedLctx xs do
        let newe ← modmapAux map e
        mkLambdaFVars xs newe
    | .forallE .. =>
      forallTelescope    e fun xs e => withmodmappedLctx xs  do
        let newe ← modmapAux map e
        mkForallFVars xs newe
    | .mdata _ e => modmapAux map e
    | _ => unreachable!

  withmodmappedLctx {α} (xs : Array Expr) (k : MetaM α) : MetaM α := do
    let localInsts ← Meta.getLocalInstances
    let mut lctx ← getLCtx
    for e in xs do
      let some lcdl := lctx.findFVar? e | unreachable!
      let ty ← Meta.withLCtx lctx localInsts (modmapAux map lcdl.type)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setType ty)
      let some value := lcdl.value? | continue
      let value← Meta.withLCtx lctx localInsts (modmapAux map value)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setValue value)
    Meta.withLCtx lctx localInsts <| k

def modmap (map : ModularMap) (e : Expr) : MetaM Expr := do
  let e ← modmapAux map e
  Meta.check e
  return e
