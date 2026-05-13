module

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
  let Expr.const c us := fn | return none
  let some info ← getMatcherInfo? c | return none
  assert! args.size >= info.arity
  let matchType ←  lambdaTelescope args[info.getMotivePos]! fun xs t => mkForallFVars xs t
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
    let k := if let Expr.const k _ := (← _root_.modMap (mkConst n us)) then k else n
    return Pattern.ctor k us (← ps.mapM _root_.modMap) (← fields.mapM modMap)
  | Pattern.as x p h            => return Pattern.as x (← p.modMap) h
  | Pattern.arrayLit t xs       => return Pattern.arrayLit (← _root_.modMap t) (← xs.mapM modMap)
  | p                   => return p

def MatcherBundle.modMap (m : MatcherBundle) (newRhss : Array Expr): ModularM MatcherBundle := do
  let {discrs, matchType, lhss, ..} := m
  -- We discard the previous rhss here since we have already modmapped them and stored in the match extension. The reason we need to do that is that if these are not modmapped early, there is no easy way to know if the rhs might contain new matchers that need extension as well
  let discrs ← discrs.mapM fun ⟨expr, h?⟩ => do return ⟨← _root_.modMap expr, h?⟩
  trace[Modular.Match] "translated discrs : {discrs.map Discr.expr}"
  trace[Modular.Match] "old matchType : {matchType}"
  let matchType ← _root_.modMap matchType
  let lhss ← lhss.mapM fun {ref, fvarDecls, patterns} => do
    --TODO put behind a function
    trace[Modular.Match] "old fvarDecls : {fvarDecls.map fun ldecl => Expr.fvar ldecl.fvarId}"
    let modMappedLCtx ← getModMappedLCtx
    -- We have to maintain both the correct original pattern context (by bookkeeping the visited fvar decls) and the modmapped context (modMappedLCtx) for `modMap` to work correctly. Once that's done, the modmapped `fvarDecls` can be fetched out of the modmapped context.
    let (modMappedLCtx, oldFvarDecls) ← fvarDecls.foldlM (init := (modMappedLCtx,[])) fun (modMappedLCtx, prevOldFvarDecls) lcdl => do
      withExistingLocalDecls prevOldFvarDecls do
      withSetModMappedLCtx modMappedLCtx do
        let ty ← _root_.modMap lcdl.type
        let modMappedLcdl := lcdl.setType ty
        return (modMappedLCtx.addDecl modMappedLcdl, lcdl::prevOldFvarDecls)
    let oldFvarDecls := oldFvarDecls.reverse
    let fvarDecls := oldFvarDecls.map (modMappedLCtx.get! ·.fvarId)
    let patterns ←
      withExistingLocalDecls oldFvarDecls do
      withSetModMappedLCtx modMappedLCtx do
        patterns.mapM Pattern.modMap
    trace[Modular.Match] "patterns : {← patterns.mapM (Pattern.toExpr · true)}"
    return {ref, fvarDecls, patterns : AltLHS}
  trace[Modular.Match] "lhss translated"
  -- let rhss ← rhss.mapM _root_.modMap
  -- trace[Modular.Match] "rhss translated"
  return {discrs, matchType, lhss, rhss := newRhss : MatcherBundle}

/- Same as the core version, except it throws an error rather than log one-/
def reportMatcherResultErrors' (altLHSS : List AltLHS) (result : MatcherResult) : TermElabM Unit := do
  unless result.counterExamples.isEmpty do
    withHeadRefOnly <| throwError m!"Missing cases:\n{Meta.Match.counterExamplesToMessageData result.counterExamples}"
    return ()
  unless match.ignoreUnusedAlts.get (← getOptions) || result.unusedAltIdxs.isEmpty do
    let mut i := 0
    for alt in altLHSS do
      if result.unusedAltIdxs.contains i then
        withRef alt.ref do withInPattern do withExistingLocalDecls alt.fvarDecls do
          let pats ← alt.patterns.mapM fun p => return toMessageData (← Pattern.toExpr p)
          let pats := MessageData.joinSep pats ", "
          throwError (mkRedundantAlternativeMsg none pats)
      i := i + 1


def MatcherBundle.mkMatcher (m : MatcherBundle) (addedAlts : Array TermMatchAltView): TermElabM Expr := do
  let {discrs := oldDiscrs, matchType, lhss := oldlhss, rhss := oldrhss} := m
  unless oldlhss.length == oldrhss.size do
    throwError "Unexpected error: number of lhs ({oldlhss.length}) and rhs ({oldrhss.size}) in original match differ"
  trace[Modular.Match] "addedAlts: {addedAlts.map MatchAltView.ref}"
  let (discrs, matchType, newlhss, newrhss) ← commitIfDidNotPostpone do
    let matchAlts ← liftMacroM <| expandMacrosInPatterns addedAlts
    trace[Modular.Match] "matchType: {matchType}"
    -- We disallow generalisations for now here, namely because it makes the task of figuring out how to update the old alts much more complex, since new patterns may be added to either the beginning (for new indices) or the right (for generalizations) of the old patterns. This is certainly managable in practice, just not a priority for now.
    let (discrs, matchType, alts, _) ← elabMatchAltViews false oldDiscrs matchType matchAlts
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
  reportMatcherResultErrors' lhss matcherResult
  trace[Modular.Match] "errors reported"
  matcherResult.addMatcher
  trace[Modular.Match] "matcher added"
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r (discrs.map Discr.expr)
  let r := mkAppN r rhss
  trace[Modular.Match] "result: {r}"
  return r
