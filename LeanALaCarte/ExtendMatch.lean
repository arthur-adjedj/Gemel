
import Lean
import LeanALaCarte.ModMap
open Lean Elab Term Meta Match

structure MatcherBundle where
  discrs : Array (Expr × DiscrInfo)
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
  let discrs := discrsExpr.toArray.zip info.discrInfos
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

partial def Lean.Meta.Match.Pattern.modMap (map : ModularMap) : Pattern → MetaM Pattern
  | Pattern.inaccessible e      => return Pattern.inaccessible (← _root_.modMap map e)
  | Pattern.val e               => return Pattern.val (← _root_.modMap map e)
  | Pattern.ctor n us ps fields => do
    -- TODO sanitize modmap extension API to make sure constructors are never extended by something other than a constructor
    let some {expr := Expr.const n _,..} := map[n]? | unreachable! --TODO better fallback
    return Pattern.ctor n us (← ps.mapM (_root_.modMap map)) (← fields.mapM (·.modMap map))
  | Pattern.as x p h            => return Pattern.as x (← p.modMap map) h
  | Pattern.arrayLit t xs       => return Pattern.arrayLit (← _root_.modMap map t) (← xs.mapM (·.modMap map))
  | p                   => return p

def MatcherBundle.modMap (map : ModularMap) (m : MatcherBundle) : MetaM MatcherBundle := do
  let {discrs, matchType, lhss, rhss} := m
  let discrs ← discrs.mapM fun (expr, h?) => do return (← _root_.modMap map expr, h?)
  let matchType ← _root_.modMap map matchType
  let rhss ← rhss.mapM (_root_.modMap map)
  return {discrs, matchType, lhss, rhss}

def MatcherBundle.mkMatcher (m : MatcherBundle) : TermElabM Expr := do
  let {discrs, matchType, lhss, rhss} := m
  let numDiscrs := discrs.size
  let matcherName ← mkAuxName `match
  let matcherResult ← Lean.Elab.Term.mkMatcher { matcherName, matchType, lhss, discrInfos := discrs.map Prod.snd}
  reportMatcherResultErrors lhss matcherResult
  matcherResult.addMatcher
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r (discrs.map Prod.fst)
  let r := mkAppN r rhss
  trace[Elab.match] "result: {r}"
  return r

/- TODO reuse match delaborator to gather the right informations about a previous match, namely:
  - take and elaborate the new branches given by the users
  - add those to the matcher infos
  - generate the appropriate matcher application
Issues:
  - What if the "new" matcher needs to be refined more than the original, how to do that ?
  - How to adapt matchers with horizontal extensions ?
-/
