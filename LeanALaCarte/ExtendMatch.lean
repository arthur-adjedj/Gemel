module

public import Lean
public import LeanALaCarte.ModMap
import all Lean.Elab.Match

public meta section

open Lean Elab Term Meta Match

structure MatcherBundle where
  discrs : Array Discr
  matchType : Expr
  lhss : List AltLHS
  rhss : Array Expr

def mkMatcherBundle (e : Expr) : MetaM (Option MatcherBundle) := do
  trace[Modular.Match] "mkMatcherBundle {e}"
  e.withApp fun fn args => do
  -- Check that this is a matcher, and then set up overapplication.
  let Expr.const c us := fn | return none
  let some info ← getMatcherInfo? c | return none
  -- TODO handle overapplication.
  assert! args.size >= info.arity
  let matchType ←  lambdaTelescope args[info.getMotivePos]! fun xs t => mkForallFVars xs t
  -- First pass visiting the match application. Incrementally fills `AppMatchState`,
  -- collecting information needed to delaborate the patterns and RHSs.
  -- No need to visit the parameters themselves.
  let params := args[0...info.numParams]
  trace[Modular.Match] "matcher params : {params}"
  let matcherType ← instantiateForall (← instantiateTypeLevelParams (← getConstVal c) us) params
  trace[Modular.Match] "matcherType : {matcherType}"
  let discrsExpr := args[info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs)]
  let discrs := discrsExpr.toArray.zipWith (bs := info.discrInfos) fun e h => ⟨e,h.1.map (TSyntax.raw ∘ mkIdent)⟩
  let rhss := args[info.getFirstAltPos...(info.getFirstAltPos + info.numAlts)]
  forallBoundedTelescope matcherType (some 1) fun _ ty => do
    let altTys ← forallTelescopeReducing ty fun matchBinders _ => matchBinders[info.numDiscrs...info.numDiscrs + info.numAlts].toArray.mapM inferType
    trace[Modular.Match] "altTys : {altTys}"
    trace[Modular.Match] "rhss : {rhss}"
    let lhss : Array AltLHS ← altTys.mapM fun altTy => forallTelescopeReducing altTy fun xs body => do
      let xs ← xs.filterM fun x => dependsOn body x.fvarId!
      body.withApp fun _motive margs => do
      let pats ←  margs.mapM toPattern
      let fvarDecls ← xs.mapM fun fvar => fvar.fvarId!.getDecl
      return { ref := .missing
               fvarDecls := fvarDecls.toList
               patterns := pats.toList }
    return some {discrs, matchType, lhss := lhss.toList, rhss}

partial def Lean.Meta.Match.Pattern.modMap : Pattern → ModularM Pattern
  | Pattern.inaccessible e      => return Pattern.inaccessible (← _root_.modMap e)
  | Pattern.val e               => return Pattern.val (← _root_.modMap e)
  | Pattern.ctor n us ps fields => do
    -- TODO sanitize modmap extension API to make sure constructors are never extended by something other than a constructor
    let some {expr := Expr.const k _,..} := (← getMap)[n]? | unreachable! --TODO better fallback
    return Pattern.ctor k us (← ps.mapM _root_.modMap) (← fields.mapM modMap)
  | Pattern.as x p h            => return Pattern.as x (← p.modMap) h
  | Pattern.arrayLit t xs       => return Pattern.arrayLit (← _root_.modMap t) (← xs.mapM modMap)
  | p                   => return p

def MatcherBundle.modMap (m : MatcherBundle) : ModularM MatcherBundle := do
  let {discrs, matchType, lhss, rhss} := m
  let discrs ← discrs.mapM fun ⟨expr, h?⟩ => do return ⟨← _root_.modMap expr, h?⟩
  trace[Modular.Match] "translated discrs : {discrs.map Discr.expr}"
  trace[Modular.Match] "old matchType : {matchType}"
  let matchType ← _root_.modMap matchType
  let lhss ← lhss.mapM fun {ref, fvarDecls, patterns} => do
    --TODO put behind a function
    let fvarDecls ← fvarDecls.foldlM (init := []) fun prevFvarDecls fvar => do
      withExistingLocalDecls prevFvarDecls do
        let ty ← _root_.modMap fvar.type
        return (fvar.setType ty)::prevFvarDecls
    let fvarDecls := fvarDecls.reverse
    let patterns ← withExistingLocalDecls fvarDecls do patterns.mapM Pattern.modMap
    trace[Modular.Match] "patterns : {← patterns.mapM (Pattern.toExpr · true)}"
    return {ref, fvarDecls, patterns : AltLHS}
  trace[Modular.Match] "lhss translated"
  let rhss ← rhss.mapM _root_.modMap
  trace[Modular.Match] "rhss translated"
  return {discrs, matchType, lhss, rhss : MatcherBundle}

def MatcherBundle.mkMatcher (m : MatcherBundle) (addedAlts : Array TermMatchAltView): TermElabM Expr := do
  let {discrs := oldDiscrs, matchType, lhss := oldlhss, rhss := oldrhss} := m
  unless oldlhss.length == oldrhss.size do
    throwError "Unexpected error: number of lhs ({oldlhss.length}) and rhs ({oldrhss.size}) in original match differ"
  trace[Modular.Match] "addedAlts: {addedAlts.map MatchAltView.ref}"
  let (discrs, matchType, newlhss, newrhss) ← commitIfDidNotPostpone do
    let matchAlts ← liftMacroM <| expandMacrosInPatterns addedAlts
    trace[Modular.Match] "matchType: {matchType}"
    let (discrs, matchType, alts, _) ← elabMatchAltViews true oldDiscrs matchType matchAlts --TODO allow generalisations ?
    trace[Modular.Match] "alts elaborated"
    synthesizeSyntheticMVarsUsingDefault
    let rhss := alts.map Prod.snd
    let matchType ← instantiateMVars matchType
    trace[Modular.Match] "matchType : {matchType}"
    let altLHSS ← instantiateAltLHSs (alts.map Prod.fst)
    trace[Modular.Match] "altLHSS instantiated"
    return (discrs, matchType, altLHSS, rhss)
  -- If the new branches need some indices to be generalized, we assume they can simply be generalised to variables in the previous branches since the information regarding those indices was useless until now. If this doesn't work, I will probably need to rewrite a version of `elabMatchAltViews` that also generalizes elaborated AltLHSs on the go, which I would much rather avoid doing...
  let mut updatedOldLhss := #[]
  let mut updatedOldRhss := #[]
  let numNewDiscrs := discrs.size - oldDiscrs.size
  trace[Modular.Match] "new discrs : {discrs[0...numNewDiscrs].toArray.map Discr.expr}"
    for {ref, fvarDecls, patterns} in oldlhss, rhs in oldrhss do
      let mut fvarDecls := fvarDecls
      let mut patterns := patterns
      let mut newRhs := rhs
      for {expr := newIndex, ..} in discrs[0...numNewDiscrs] do
        let indexType ← inferType newIndex
        let newldcl ← withLocalDecl `x .default indexType fun fvar => FVarId.getDecl fvar.fvarId!
        fvarDecls ← fvarDecls.mapM fun ldcl => do
          let ty := (← kabstract ldcl.type newIndex).instantiate1 (Expr.fvar newldcl.fvarId)
          pure (ldcl.setType ty)
        fvarDecls := newldcl::fvarDecls
        -- This feels so hacky............
        patterns ← patterns.mapM fun pat => do
          let e ← pat.toExpr
          let e ← kabstract e newIndex
          let e := e.instantiate1 (Expr.fvar newldcl.fvarId)
          trace[Modular.Match] "pattern generalisation: {e}"
          ToDepElimPattern.toPattern e
        patterns := (Pattern.var newldcl.fvarId)::patterns
        newRhs ← kabstract newRhs newIndex
        newRhs := Expr.lam `x indexType newRhs .default
        trace[Modular.Match] "rhs generalisation: from {rhs} to {newRhs}"
      updatedOldRhss := updatedOldRhss.push newRhs
      updatedOldLhss := updatedOldLhss.push {ref, fvarDecls, patterns}
  let lhss := updatedOldLhss.toList ++ newlhss
  let rhss := updatedOldRhss ++ newrhss
  unless lhss.length == rhss.size do
    throwError "Unexpected error: number of lhs ({lhss.length}) and rhs ({rhss.size}) in generated match differ"
  let numDiscrs := discrs.size
  let matcherName ← mkAuxName `match
  trace[Modular.Match] "matcherName : {matcherName}"
  let matcherResult ← Lean.Elab.Term.mkMatcher { matcherName, matchType, lhss, discrInfos := discrs.map fun ⟨_,h⟩ => ⟨h.map Syntax.getId⟩}
  trace[Modular.Match] "matcherResult generated"
  reportMatcherResultErrors lhss matcherResult
  trace[Modular.Match] "errors reported"
  matcherResult.addMatcher
  trace[Modular.Match] "matcher added"
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r (discrs.map Discr.expr)
  let r := mkAppN r rhss
  trace[Modular.Match] "result: {r}"
  return r
