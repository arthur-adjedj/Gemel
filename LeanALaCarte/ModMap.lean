module

public import LeanALaCarte.Elab
public import LeanALaCarte.ModularCommand

@[expose] public meta section

open Lean Meta Elab Command Term

partial def modMapAux (e : Expr): ModularM Expr := do
  withIncRecDepth do
  -- withNewMCtxDepth do
  withTraceNode `Modular.Subst (λ exn => return m!"modMapAux {indentExpr e} \n⇒{exn.toOption.map indentExpr}") do e.withApp fun fn args => do
  if let .const fnName lvls := fn then -- TODO manage universes better
    -- If a constant is not already extended at this point but should be (e.g if its type contains things that have a partial map), one might want, to delta-reduce the constant and map it as well.
    -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constants topographically to ensure this.
    if let some ext := (← getMap)[fnName.eraseMacroScopes]? then
      --If the partial map has more args than given in the term, we need to eta-expand to avoid producing a term with loose bvars.
      unless ext.numArgs <= args.size do
        return ← modMapAux (← Meta.etaExpand e)
      let newArgs ← modMapArgs args
      let res := ext.expr
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
      -- Let's just `check` the entire translated expression in `modmap` instead. Hopefully it's okay..
      -- if ext.numArgs != 0 then
        -- check res  --typecheck the result, which should give a sensible type to each synthetic mvar introduced in the term, and throw a type-error if the generated term is ill-formed.
        -- TODO For (much) better performance in the future, rather than `check` every translation that introduces an mvar, it would make a lot more sense to store the information necessary to infer the type of those mvars in the `ModularExtension`s, I just haven't thought hard enough about how to do that well for now
      let res ← instantiateMVars res
      return res
    let fallback _ : ModularM Expr := do
      let newArgs ← modMapArgs args
      pure (mkAppN fn newArgs)
    let some info ← getMatcherInfo? fnName | fallback ()
    trace[Modular.Subst] "matcher {fnName} detected"
    let mvarLCtx ← getLCtx
    forallTelescopeReducing (← inferType fn) fun xs _ => do
      let discrs_ty_hds ← xs[info.getFirstDiscrPos...info.getFirstDiscrPos+info.numDiscrs].toArray.mapM (inferType · >>= (fun e => whnf e) >>= pure ∘ Expr.getAppFn)
      trace[Modular.Subst] "discrs_ty_hds : {discrs_ty_hds}"
      -- If one of the discriminants is an extended type, we hide the entire match behind a metavariable, save the original matcher somewhere, and replace the whole thing with a new matcher with extended arm
      for hd in discrs_ty_hds do
        let some ⟨hd_name,_⟩ := hd.const? |
          throwError "That's unexpected, expected a function head, found {hd}"
        if (← getMap).contains hd_name then
          let mvar_ty ← withLCtx' mvarLCtx (inferType e >>= modMapAux)
          trace[Modular.Subst] "new matcher type : {mvar_ty}"
          let mvar ← withLCtx' mvarLCtx <| mkFreshExprMVar mvar_ty .syntheticOpaque
          trace[Modular.Subst] "matcher mvar : {mvar}"
          return mvar
      fallback ()
  else
    let newFn ← traverse fn
    let newArgs ← modMapArgs args
    return mkAppN newFn newArgs
where
  modMapArgs args := args.foldlM (init := Array.emptyWithCapacity args.size) fun nargs e => do
    let arg ← modMapAux e
    return nargs.push arg

  traverse e: ModularM Expr := match e with
    | .sort _
    | .lit _ --What if you extend Nat/String ? you probably want literals to be translated accordingly, but that's an edge-case not worth thinking about for now
    | .bvar _ | .fvar _ | .mvar _ => pure e
    | .proj tyName idx struct => do
      if let some _ext := (← getMap)[tyName.eraseMacroScopes]? then
        /- Plan here:
           - look into `ext.translation`, make sure its head is a constant that is structureLike (otherwise throw an exception, we cannot produce "projections" for a type that has more than one constructor/is indexed)
           - use the corresponding constant as the new head
           TODO what if the mapping is partial and the type contains holes ? In practice, shouldn't be an issue as said holes would morally be filled as part of the types of the mapped `struct`
        -/
        panic! "todo"
      else
        let newStruct ← modMapAux struct
        return .proj tyName idx newStruct
    | .letE ..
    | .lam .. =>
      lambdaLetTelescope e fun xs e => withmodMappedLctx xs do
        let newe ← modMapAux e
        mkLambdaFVars xs newe
    | .forallE .. =>
      forallTelescope    e fun xs e => withmodMappedLctx xs  do
        let newe ← modMapAux e
        mkForallFVars xs newe
    | .mdata _ e => modMapAux e
    | _ => unreachable!

  withmodMappedLctx {α} (xs : Array Expr) (k : ModularM α) : ModularM α := do
    let localInsts ← Meta.getLocalInstances
    let mut lctx ← getLCtx
    for e in xs do
      let some lcdl := lctx.findFVar? e | unreachable!
      let ty ← Meta.withLCtx lctx localInsts (modMapAux lcdl.type)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setType ty)
      let some value := lcdl.value? | continue
      let value← Meta.withLCtx lctx localInsts (modMapAux value)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setValue value)
    Meta.withLCtx lctx localInsts <| k

def modMap (e : Expr) : ModularM Expr := do
  let e ← modMapAux e
  Meta.check e
  return e
