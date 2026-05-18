module

public import LeanALaCarte.Elab
public meta import LeanALaCarte.Elab
public meta import LeanALaCarte.Util

public meta section

open Lean Meta Elab Command Term

-- The main context in which this runs is the original context, not the modmapped one!
partial def modMapAux (e : Expr): ModularM Expr := do
  withIncRecDepth do
  withTraceNode `Modular.Subst (λ exn => return m!"modMapAux {indentExpr e} \n⇒{← (withModMappedLCtx do return exn.toOption.map indentExpr)}") do
  e.withApp fun fn args => do
  -- TODO manage universes better
  let .const fnName lvls := fn | return mkAppN (← traverse fn) (← modMapArgs args)
  -- If a constant is not already extended at this point but should be (e.g if its type contains things that have a partial map), one might want, to delta-reduce the constant and map it as well.
  -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constants topographically to ensure this.
  if let some ext := (← getMap)[fnName.eraseMacroScopes]? then
    --If the partial map has more args than given in the term, we need to eta-expand to avoid producing a term with loose bvars.
    unless ext.numArgs <= args.size do
      let e ← Meta.etaExpand e
      return (← withTraceNode `Modular.Subst (fun _ => return m!"Eta-expanding expression") do modMapAux e)
    let newArgs ← modMapArgs args
    let res := ext.expr
      |>.instantiateLevelParams ext.levelParams lvls
      |>.instantiateRev newArgs[:ext.numArgs]
    let res ← modMapAux res
    trace[Modular.Subst] m!"args instantiated : {res}"
    trace[Modular.Subst] m!"numHoles : {ext.numHoles}"
    -- The produced mvars are "synthetic", i.e they ought to be resolved by the users using tactics or other automations rather than through unification. We may want to use some heuristics in some cases to resolve these automatically when possible.
    let mvars ← withModMappedLCtx do Array.mkM ext.numHoles (mkFreshExprMVar none .syntheticOpaque)
    trace[Modular.Subst] m!"mvars : {mvars}"
    let res := res.instantiateRev mvars
    trace[Modular.Subst] m!"mvars instantiated : {res}"
    let res := mkAppN res newArgs[ext.numArgs:]
    trace[Modular.Subst] m!"with extra args : {res}"
    return res
  let fallback _ : ModularM Expr := do
    let newArgs ← modMapArgs args
    let res := (mkAppN fn newArgs)
    pure res
  let some info ← getMatcherInfo? fnName | fallback ()
  trace[Modular.Subst] "matcher {fnName} detected"
  unless ← shouldAbstractMatcher info fn do
    return ← fallback ()
  let mvar ← do
    let mvar_ty ← modMapAux (← inferType e)
    trace[Modular.Subst] "new matcher type : {mvar_ty}"
    withLCtx' (← getModMappedLCtx) do mkFreshExprMVar mvar_ty .syntheticOpaque
  trace[Modular.Subst] "matcher mvar : {mvar}"
  -- We must compute the modmapped rhss early to report of any potential matchers needing extension
  let rhss ← modMapArgs args[info.getFirstAltPos...(info.getFirstAltPos + info.numAlts)]
  addMatchExtension { matchName := fnName
                      mvar := mvar.mvarId!
                      originalMatch := e
                      modMappedRhss := rhss
                      originalLCtx := ← getLCtx }
  return mvar

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
      lambdaLetTelescope e fun xs e => do
        let modMappedctx ← withAddModMappedFVars xs
        withSetModMappedLCtx modMappedctx do
          let e ← modMapAux e
          withModMappedLCtx do Meta.check e
          withLCtx' modMappedctx do mkLetFVars xs e (generalizeNondepLet := false)
    | .forallE .. =>
      forallTelescope e fun xs e => do
        let modMappedctx ← withAddModMappedFVars xs
        withSetModMappedLCtx modMappedctx do
          let e ← modMapAux e
          withModMappedLCtx do Meta.check e
          withLCtx' modMappedctx do mkForallFVars xs e
    | .mdata m e => return .mdata m (← modMapAux e)
    | _ => unreachable!

  withAddModMappedFVars (xs : Array Expr) : ModularM LocalContext := do
    let mut modMappedLCtx ← getModMappedLCtx
    for e in xs do
      let some lcdl := (← getLCtx).findFVar? e | unreachable!
      assert! modMappedLCtx.findFVar? e |>.isNone
      let newLcdl : LocalDecl ← withSetModMappedLCtx modMappedLCtx do
        match lcdl with
        | .cdecl i fvarId u ty bi   k => return LocalDecl.cdecl i fvarId u (← modMapAux ty) bi k
        | .ldecl i fvarId u ty v nd k => return LocalDecl.ldecl i fvarId u (← modMapAux ty) (← modMapAux v) nd k
      modMappedLCtx := modMappedLCtx.addDecl newLcdl
    return modMappedLCtx

  shouldAbstractMatcher (info : MatcherInfo) (e : Expr) : ModularM Bool := do
    forallTelescopeReducing (← inferType e) fun xs _ => do
      let discrs_fvars := xs[info.getFirstDiscrPos...info.getFirstDiscrPos+info.numDiscrs]
      trace[Modular.Subst] "discrs_fvars : {discrs_fvars}"
      let modMappedctx ← withAddModMappedFVars xs
      for hd_fvar in discrs_fvars do
        let ty ← inferType hd_fvar
        let mod_ty ← withSetModMappedLCtx modMappedctx do modMapAux ty
        if ty != mod_ty then
          return true
      return false

def modMap (e : Expr) : ModularM Expr :=
  prependError m!"Failed to translate expression {indentExpr e}:" do
  let e ← modMapAux e
  -- withModMappedLCtx do Meta.check e
  return e
