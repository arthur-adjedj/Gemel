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

def mkMatcherBundle (e : Expr) : MetaM (Option MatcherBundle) :=
  e.withApp fun fn args => do
  -- Check that this is a matcher, and then set up overapplication.
  let Expr.const c us := fn | return none
  let some info ← getMatcherInfo? c | return none
  -- TODO handle overapplication.
  assert! args.size >= info.arity
  -- First pass visiting the match application. Incrementally fills `AppMatchState`,
  -- collecting information needed to delaborate the patterns and RHSs.
  -- No need to visit the parameters themselves.
  let params := args[0...info.numParams]
  let matchType ← instantiateForall (← instantiateTypeLevelParams (← getConstVal c) us) params
  -- let motive := args[info.numParams...1]
  let discrsExpr := args[info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs)]
  let discrs := discrsExpr.toArray.zipWith (bs := info.discrInfos) fun e h => ⟨e,h.1.map (TSyntax.raw ∘ mkIdent)⟩
  let rhss := args[info.getFirstAltPos...(info.getFirstAltPos + info.numAlts)]
  let altTys : Array Expr ← forallTelescopeReducing matchType fun matchBinders _ => matchBinders[info.getFirstAltPos...(info.getFirstAltPos + info.numAlts)].toArray.mapM inferType
  let lhss : Array AltLHS ← altTys.mapM fun altTy =>  forallTelescopeReducing altTy fun _ e => e.withApp fun _motive margs => do
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
  let rhss ← rhss.mapM _root_.modMap
  return {discrs, matchType, lhss, rhss}

def MatcherBundle.mkMatcher (m : MatcherBundle) (addedAlts : Array TermMatchAltView): TermElabM Expr := do
  let {discrs, matchType, lhss, rhss} := m
  let (discrs, matchType, newlhss, newrhss) ← commitIfDidNotPostpone do
    let matchAlts ← liftMacroM <| expandMacrosInPatterns addedAlts
    trace[Elab.match] "matchType: {matchType}"
    let (discrs, matchType, alts, _) ← elabMatchAltViews false discrs matchType matchAlts --TODO allow generalisations ?
    synthesizeSyntheticMVarsUsingDefault
    let rhss := alts.map Prod.snd
    let matchType ← instantiateMVars matchType
    let altLHSS ← instantiateAltLHSs (alts.map Prod.fst)
    return (discrs, matchType, altLHSS, rhss)
  let lhss := lhss ++ newlhss
  let rhss := rhss ++ newrhss
  let numDiscrs := discrs.size
  let matcherName ← mkAuxName `match
  let matcherResult ← Lean.Elab.Term.mkMatcher { matcherName, matchType, lhss, discrInfos := discrs.map fun ⟨_,h⟩ => ⟨h.map Syntax.getId⟩}
  reportMatcherResultErrors lhss matcherResult
  matcherResult.addMatcher
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r (discrs.map Discr.expr)
  let r := mkAppN r rhss
  trace[Elab.match] "result: {r}"
  return r
