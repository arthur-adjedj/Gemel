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
  forallBoundedTelescope matcherType (some <| info.numParams + 1) fun _ ty => do
    let altTys : Array Expr ← forallTelescopeReducing ty fun matchBinders _ => matchBinders[info.numDiscrs...info.numDiscrs+ info.numAlts].toArray.mapM inferType
    trace[Modular.Match] "altTys : {altTys}"
    let lhss : Array AltLHS ← altTys.mapM fun altTy => forallTelescopeReducing altTy fun _ e => e.withApp fun _motive margs => do
      let pats ←  margs.mapM toPattern
      let (_,fvars) ← (pats.forM Pattern.collectFVars).run {}
      let fvarDecls ← fvars.fvarIds.mapM FVarId.getDecl
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
  let matchType ← _root_.modMap matchType
  let lhss ← lhss.mapM fun {ref, fvarDecls, patterns} => do
    let fvarDecls ← fvarDecls.mapM fun --TODO this should be its own function
      | .cdecl index fvarId userName type bi kind => do
        return .cdecl index fvarId userName (← _root_.modMap type) bi kind
      | .ldecl index fvarId userName type value nondep kind => do
        return .ldecl index fvarId userName (← _root_.modMap type) (← _root_.modMap value) nondep kind
    let patterns ← patterns.mapM Pattern.modMap
    return {ref, fvarDecls, patterns : AltLHS}
  let rhss ← rhss.mapM _root_.modMap
  return {discrs, matchType, lhss, rhss}

def MatcherBundle.mkMatcher (m : MatcherBundle) (addedAlts : Array TermMatchAltView): TermElabM Expr := do
  let {discrs, matchType, lhss, rhss} := m
  trace[Modular.Match] "addedAlts: {addedAlts.map MatchAltView.ref}"
  let (discrs, matchType, newlhss, newrhss) ← commitIfDidNotPostpone do
    let matchAlts ← liftMacroM <| expandMacrosInPatterns addedAlts
    trace[Modular.Match] "matchType: {matchType}"
    let (discrs, matchType, alts, _) ← elabMatchAltViews false discrs matchType matchAlts --TODO allow generalisations ?
    trace[Modular.Match] "alts elaborated"
    synthesizeSyntheticMVarsUsingDefault
    let rhss := alts.map Prod.snd
    let matchType ← instantiateMVars matchType
    trace[Modular.Match] "matchType : {matchType}"
    let altLHSS ← instantiateAltLHSs (alts.map Prod.fst)
    trace[Modular.Match] "altLHSS instantiated"
    return (discrs, matchType, altLHSS, rhss)
  let lhss := lhss ++ newlhss
  let rhss := rhss ++ newrhss
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
