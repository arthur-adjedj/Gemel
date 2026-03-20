import LeanALaCarte.Elab
open Lean Meta Elab Command Term

partial def modmap (map : ModularMap) (e : Expr) : MetaM Expr := do
  withIncRecDepth do
  withTraceNode `Modular.Subst (λ exn => return m!"{exceptEmoji exn} modmap {e} ⇒ {exn.toOption}") do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const fnName lvls := fn then -- TODO manage universes better
    -- One might want to, if a constant is not already extended at this point but should be (e.g if its type contains things that have a partial map), delta-reduce the constant and map it as well.
    -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constants topographically to ensure this.
    let ext? := map[fnName.eraseMacroScopes]?
    if let some ext := ext? then
      --If the partial map has more args than given in the term, we need to eta-expand to avoid producing a term with loose bvars.
      unless ext.numArgs <= args.size do
        return ← modmap map (← Meta.etaExpand e)
      let newArgs ← args.mapM (modmap map)
      let res := ext.translation
        |>.instantiateLevelParams ext.levelParams lvls
        |>.instantiateRev newArgs[:ext.numArgs]
      trace[Modular.Subst] m!"args instantiated : {res}"
      trace[Modular.Subst] m!"numHoles : {ext.numHoles}"
      -- The produced mvars are "synthetic", i.e they ought to be resolved by the users using tactics or other automations rather than through unification. We may want to use some heuristics in some cases to resolve these automatically when possible.
      let mvars ← Array.mkM ext.numHoles (mkFreshExprMVar none .synthetic)
      trace[Modular.Subst] m!"mvars : {mvars}"
      let res := res.instantiateRev mvars
      trace[Modular.Subst] m!"mvars instantiated : {res}"
      let res := mkAppN res newArgs[ext.numArgs:]
      trace[Modular.Subst] m!"with extra args : {res}"
      check res --typecheck the result, which should give a sensible type to each synthetic mvar introduced in the term, and throw a type-error if the generated term is ill-formed.
      return res
    else return mkAppN fn (← args.mapM (modmap map))
  else return mkAppN (← go fn) (← args.mapM (modmap map))
where
  go e : MetaM Expr := match e with
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
        return .proj tyName idx (← modmap map struct)
    | .letE ..
    | .lam .. =>
      lambdaLetTelescope e fun xs e => withModMappedLctx xs do
        mkLambdaFVars xs (← modmap map e)
    | .forallE .. =>
      forallTelescope e fun xs e => withModMappedLctx xs do
        mkForallFVars xs (← modmap map e)
    | .mdata _ e => modmap map e
    | _ => unreachable!

  withModMappedLctx {α} (xs : Array Expr) (k : MetaM α) : MetaM α := do
    let localInsts ← Meta.getLocalInstances
    let mut lctx ← getLCtx
    for e in xs do
      let some lcdl := lctx.findFVar? e | unreachable!
      let ty ← Meta.withLCtx lctx localInsts (modmap map lcdl.type)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setType ty)
      let some value := lcdl.value? | continue
      let value ← Meta.withLCtx lctx localInsts (modmap map value)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setValue value)
    Meta.withLCtx lctx localInsts k
