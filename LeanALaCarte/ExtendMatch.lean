module

public import LeanALaCarte.ModMap
public import LeanALaCarte.MergeModMaps
import all Lean.Elab.Match

public meta section

open Lean Elab Term Meta Match

instance : ToMessageData Pattern where
  toMessageData := Pattern.toMessageData

structure MatcherBundle where
  lctx : LocalContext
  discrs : Array Discr
  matchType : Expr
  lhss : List AltLHS
  rhss : Array Expr
deriving Inhabited

def MatcherBundle.replaceLCtx (m : MatcherBundle) (lctx : LocalContext) : MatcherBundle := Id.run do
  let oldFVars := m.lctx.getFVarIds
  let newFVars := lctx.getFVars
  let mut subst : FVarSubst := .empty
  for oldFVar in oldFVars, newFVar in newFVars do
    subst := subst.insert oldFVar newFVar
  { lctx := lctx
    discrs := m.discrs.map fun ⟨e,h?⟩ => ⟨subst.apply e,h?⟩
    matchType := subst.apply m.matchType
    lhss := m.lhss.map fun ⟨ref,fvarDecls,patterns⟩ => ⟨ref,fvarDecls.map (LocalDecl.applyFVarSubst subst),patterns.map (Match.Pattern.applyFVarSubst subst)⟩
    rhss := m.rhss.map subst.apply }

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
  let lctx ← getLCtx
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
    return some {lctx, discrs, matchType, lhss := lhss.toList, rhss}

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
  let lctx ← getModMappedLCtx
  return {lctx, discrs, matchType, lhss, rhss := newRhss : MatcherBundle}

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

def MatcherBundle.mkMatcher (m : MatcherBundle) (addedAlts : Array TermMatchAltView): TermElabM Expr :=
  withTraceNode `Modular.Match (fun | .ok _ => return "Generating matcher from matcher bundle and added alts"
                                    | .error e => return m!"Generating matcher from matcher bundle and added alts {e.toMessageData}") do
  let {lctx, discrs := oldDiscrs, matchType, lhss := oldlhss, rhss := oldrhss} := m
  withLCtx' lctx do
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
    trace[Modular.Match] "fvars before: {fvarDecls.map fun fvarDecl => fvarDecl.fvarId.name}"
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
    trace[Modular.Match] "fvars after: {fvarDecls.map fun fvarDecl => fvarDecl.fvarId.name}"
    updatedOldRhss := updatedOldRhss.push newRhs
    updatedOldLhss := updatedOldLhss.push {ref, fvarDecls, patterns}
  let lhss := updatedOldLhss.toList ++ newlhss
  let rhss := updatedOldRhss ++ newrhss
  trace[Modular.Match] "lhss : {← lhss.mapM fun lhs => lhs.patterns.mapM fun p => p.toExpr}"
  trace[Modular.Match] "rhss : {rhss}"
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

structure MatchClause where
  ref  : Syntax
  name : Name
  argNames : Array Name
  alts : Array Term.TermMatchAltView

def elabModularWhereMatch (stx : Syntax) : MatchClause :=
  let name := stx[1].getId
  let argNames := stx[2].getArgs.map Syntax.getId
  let alts := stx[4].getArgs.filterMap (Term.getMatchAlt `term)
  { ref := stx, name, argNames, alts }

-- TODO this doesn't seem to work anymore ? investigate..
def withArgNames [Monad m] [self : MonadLCtx m] [MonadControlT MetaM m] (argNames : Array Name) (k : m α): m α := do
  let mut lctx ← getLCtx
  let hyps ← getLocalHyps
  for argName in argNames, hyp in hyps do
    lctx := lctx.setUserName hyp.fvarId! argName
  withLCtx' lctx k

def _root_.Lean.LocalContext.toMessageData (lctx : LocalContext) : MessageData :=
  let fvarNames := lctx.getFVarIds.map (fun fvar => fvar.name)
  m!"{fvarNames}"
  -- withLCtx' lctx do
    -- let mvar ← mkFreshExprMVar none
    -- return m!"{mvar.mvarId!}"

deriving instance BEq for Pattern

def mergeBranches (oldlhss newlhss : Array AltLHS) (oldrhss newrhss : Array Expr) : ModularM (Array AltLHS × Array Expr) := do
  assert! oldlhss.size = oldrhss.size && newlhss.size = newrhss.size
  let mut lhss := oldlhss
  let mut rhss := oldrhss
  for i in [:newlhss.size] do
    let newlhs := newlhss[i]!
    let mut isRedundantBranch := false
    let newlhspatternExprs ← newlhss[i]!.patterns.mapM fun p =>  Pattern.toExpr p
    for j in [:oldlhss.size] do
      let oldlhs := oldlhss[j]!
      unless oldlhs.fvarDecls.length == newlhs.fvarDecls.length do
        break
      -- This reads so much like OCaml, I hate it.
      -- TODO define and use List.foldl₂ here instead
      let subst := oldlhs.fvarDecls.foldl (init := (newlhs.fvarDecls,FVarSubst.empty)) (fun
        | ([],_), _ => unreachable!
        | (newlcdl::tl,subst), oldlcdl => (tl, subst.insert oldlcdl.fvarId (Expr.fvar newlcdl.fvarId)))
        |>.2
      -- TODO this is probably too strict an equality, what if i.e one side has inaccessible terms/named patterns and the other doesn't ?
      let oldp ←  oldlhs.patterns.mapM (Pattern.toExpr $ Pattern.applyFVarSubst subst ·)
      trace[Modular.Match] "Comparing patterns {oldp} and {newlhspatternExprs}"
      unless oldp == newlhspatternExprs do
        break
      trace[Modular.Match] "They're the same thing !"
      let newrhs := newrhss[i]!
      let oldrhs := oldrhss[i]!
      let rhs ← mergeExprs #[oldrhs,newrhs]
      rhss := rhss.set! i rhs
      isRedundantBranch := true
    unless isRedundantBranch do
      lhss := lhss.push newlhs
      rhss := rhss.push newrhss[i]!
  return (lhss,rhss)

def mergeMatcherBundles (ms : Array MatcherBundle) : ModularM MatcherBundle :=
  withTraceNode `Modular.Match (fun | .ok _ => return m!"Merging matcherBundles"
                                    | .error e => return m!"Merging matcherBundles : {e.toMessageData}") do
  if _ : ms.size = 0 then
    throwError "Unexpected: empty array of matcher bundles"
  else if _ : ms.size = 1 then
    return ms[0]
  else
    let mut res := ms[0]
    for m in ms[1:] do
      let {lctx, discrs, matchType, lhss, rhss} := m.replaceLCtx res.lctx
      -- for ⟨e₁,_⟩ in res.discrs, ⟨e₂,_⟩ in discrs do
        -- TODO be more permissive eg by using isDefEq ? If so, make sure to work in the right lctx
        -- let e₁' := e₁.abstr res.lctx.getFVars
        -- let e₂' := e₂.abstract lctx.getFVars
        -- unless e₁' == e₂' do
          -- throwError "Unable to merge matches: discriminants {e₁'} and {e₂'} are not defeq."
      -- TODO be more permissive eg by using isDefEq ? If so, make sure to work in the right lctx
      -- unless res.matchType.abstract res.lctx.getFVars == matchType.abstract lctx.getFVars do
        -- throwError "Unable to merge matches: match types {res.matchType} and {matchType} are not defeq."
      -- the merging of lhss/rhss is naive and doesn't allow for diamonds here

      -- TODO this translation back and forth of the lhss between List and Array is unpleasant, but makes `mergebranches` easier to write...
      -- Such lists are also usually very short, so it should be okay. Lots of room for optimisation in that function generally if it isn't.
      let (lhss,rhss) ← mergeBranches res.lhss.toArray lhss.toArray res.rhss rhss
      res := {res with lhss := lhss.toList, rhss}
    return res

def elabModMatch (newFunName : Name) (mvar : MVarId) (matchExt : Array MatchToExtend) (matchClause : MatchClause) : ModularM Unit := do
  unless matchExt.size != 0 do
    throwError "Unexpected: attempted to extend the merging of 0 matchers"
  let {ref, name, alts, argNames} := matchClause
  if ← mvar.isAssigned then return
  withRef ref do
  -- We consider the first matcher in the array to be "canonical", in that its name will be used
  let {matchName, mvar := matchmvar, originalLCtx,..} := matchExt[0]!
  unless mvar == matchmvar do
    throwError "Internal error: expected matcher to have mvar {Expr.mvar mvar} ({Expr.mvar <| ← getDelayedMVarRoot mvar}), found {Expr.mvar matchmvar} ({Expr.mvar <| ← getDelayedMVarRoot matchmvar}) instead (All matchers' mvars : {matchExt.map (Expr.mvar ·.mvar)})"
  trace[Modular.Match] "Elaborating matcher : {name} {Expr.mvar mvar}"
  let .str _ matchName := matchName | throwError "Unexpected match name {matchName}"
  unless Name.mkSimple matchName = name do
    throwErrorAt ref[0] "Unexpected user-provided match name: expected {matchName}, found {name}"
  let mut matcherBundles := #[]
  withTraceNode `Modular.Match (fun _ => return "Generating Matcher bundles") do←
    for {matchName, mvar := matchmvar, originalMatch, originalLCtx, modMappedRhss} in matchExt do
      let mvarDecl ← matchmvar.getDecl
      withSetModMappedLCtx mvarDecl.lctx do←
      withLCtx' originalLCtx do←
        trace[Modular.Match] "originalMatch : {originalMatch}"
        trace[Modular.Match] "modMappedRhss : {modMappedRhss}"
        let some matcherBundle ← mkMatcherBundle originalMatch | throwError "Expected matcher, found {originalMatch} instead"
        trace[Modular.Match] "matcherBundle generated"
        let matcherBundle ←
          withTraceNode `Modular.Match (fun _ => return "Modmapping matcherBundle") do
            matcherBundle.modMap modMappedRhss
        trace[Modular.Match] "matcherBundle modmapped"
        trace[Modular.Match] "patterns : {alts.map (·.patterns)}"
        matcherBundles := matcherBundles.push matcherBundle
  let mvarDecl ← mvar.getDecl
  withSetModMappedLCtx mvarDecl.lctx do
  withModMappedLCtx do
  withArgNames argNames do
    let m ← mergeMatcherBundles matcherBundles
    Term.withDeclName newFunName do
      let newMatcherExpr ← MatcherBundle.mkMatcher m alts
      mvar.assign newMatcherExpr

def elabModMatchNoClauses (newFunName : Name) (mvar : MVarId) (matchExt : Array MatchToExtend) : ModularM Unit := do
  unless matchExt.size != 0 do
    throwError "Unexpected: attempted to extend the merging of 0 matchers"
  let .str _ name := matchExt[0]!.matchName | throwError "Unexpected match name {matchExt[0]!.matchName}"
  elabModMatch newFunName mvar matchExt ⟨.missing, .mkSimple name,#[],#[]⟩
