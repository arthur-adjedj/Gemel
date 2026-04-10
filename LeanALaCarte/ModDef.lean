module

public import Lean.Parser.Command
public import Lean.Parser.Tactic
public import Lean.Parser.Term
public import Lean.Elab.MutualDef
public meta import Lean.Meta.Tactic.Try
public meta import Lean.Elab.PreDefinition.Main
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Match
public meta import LeanALaCarte.ModMap
public meta import LeanALaCarte.Elab
public meta import LeanALaCarte.CollectDelayedAssignementsWithArgs
public meta import LeanALaCarte.AuxMapping
public meta import LeanALaCarte.CollectAuxDefs
public meta import LeanALaCarte.UnfoldEqns
public meta import LeanALaCarte.ExtendMatch

public meta section

open Lean Parser Elab Meta

instance : ToString Match.AltParamInfo where
  toString info :=
  let {numFields, numOverlaps, hasUnitThunk} := info
  s!"⦃ numFields : {numFields}, numOverlaps : {numOverlaps}, hasUnitThunk : {hasUnitThunk} ⦄"

instance : ToString MatcherInfo where
  toString info :=
  let {numParams, numDiscrs, altInfos, uElimPos?, ..} := info
  s!"⦃ numParams : {numParams},
  numDiscrs : {numDiscrs},
  altInfos : {altInfos},
  uElimPos? : {uElimPos?} ⦄"


def Lean.ConstantInfo.kind! (cinfo : ConstantInfo) : DefKind := match cinfo with
  | .defnInfo _ => .def
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | _ => unreachable!

def getEqDef? (n : Name) : MetaM (Option Expr) := do
  let some edn ← Try.Collector.getEqDefDecl? n | return none
  let edth ← getConstInfo edn
  forallTelescope edth.type fun xs e =>
    let_expr Eq _ _ rhs := e | unreachable!
    mkLambdaFVars xs rhs

def modMapValueOrEqDef (cinfo : ConstantInfo) (isAux : Bool) : ModularM Expr := do
  let fallback _ := modMap cinfo.value!
  if isAux then fallback ()
  else
    let some value ← getEqDef? cinfo.name | fallback ()
    modMap value

def solveGoalsWithTactic (tac : Syntax) (goals : List MVarId) : TermElabM Unit := do
  unless goals.isEmpty do
    -- make info from `runTactic` available
    goals.forM fun goal => pushInfoTree (.hole goal)
    -- assign goals
    let remainingGoals ← Tactic.run goals[0]! do
      Tactic.setGoals goals
      Tactic.withTacticInfoContext tac do
        Tactic.evalTactic tac
    -- complain if any goals remain
    unless remainingGoals.isEmpty do
      Term.reportUnsolvedGoals remainingGoals

structure MappedHeader where
  cinfo : ConstantInfo
  newName : Name
  isAux : Bool
  type : Expr
deriving Inhabited

def mkMappedDecl (oldName newName : Name) (isAux := true): ModularM MappedHeader := do
  let cinfo ← getConstInfo oldName
  let type ← modMap cinfo.type
  assert! !type.hasMVar
  return { cinfo, newName, isAux, type }

/- TODO adapt syntax to take into account:
- docstrings
- attributes
- termination hints
- `where` clauses
- (maybe ?) make the current `by` goals be filled in as holes in `where finally` ? (this would be non-trivial in cases where the holes appear in auxiliary defs rather than the "real" one. One solution could be to inline/delta-reduce auxiliary defs that aren't matchers, and translating the core def directly, leaving the job of re-abstracting relevant parts of the code to the usual elaborator for `PreDef`s. The big danger to doing that is obviously performance. `modMap`ed terms need to be `check`ed to instantiate the type of the introduced mvars for now, and doing so on terms containing very large proof terms (e.g `grind` or `omega` proofs) is bound to be expensive. A solution would be to get rid of `Meta.check` in `modMap`, but I'm confident type-checking is still called a fair few times when elaborating PreDefs, so this doesn't solve the issue of abstracting the proofs at the right time.)

Once that is all done, translate that syntax to a `DefView` and elaborate it like any other function, making use of all the niceties the lean elaborator offers :D
Actually, `DefView` contain the value as a syntax, not as an Expr, this is not ideal because it implies needing to first delaborate the translated term before re-elaborating it.. Let's try to translate things directly to `PreDef`s instead, this will be a bit of a PITA...
-/

def modular_where_match_clause := leading_parser
  Term.ident >> many Term.ident >> "with " >> checkColGt >> many Term.matchAlt

structure MatchClause where
  ref  : Syntax
  name : Name
  argNames : Array Name --TODO use that to rename context vars
  alts : Array Term.TermMatchAltView

def elabModularWhereMatch (stx : Syntax) : MatchClause :=
  let name := stx[0].getId
  let argNames := stx[1].getArgs.map Syntax.getId
  let alts := stx[3].getArgs.filterMap (Term.getMatchAlt `term)
  { ref := stx, name, argNames, alts }

syntax (name := modular_mod_def)
  declModifiers "mod_def" ident "extends" ident ("where " colGt modular_where_match_clause* ("finally " tacticSeqIndentGt)? )?  Termination.suffix : modular_command

instance : ToMessageData PreDefinition where
  toMessageData m :=
    m!"{m.declName} := {m.value} : {m.type}"

@[modular_elab modular_mod_def, incremental]
meta def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $mod:declModifiers mod_def $newFun extends $oldFun $[where $match_clauses* $[finally $tacs]?]?  $termination_stx) => liftModularM do withRef stx do
    let modifiers ← elabModifiers mod
    let modifiers := modifiers
    let termination_hint ← elabTerminationHints termination_stx
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun
    let newFunName := (← getCurrNamespace) ++ newFun.getId
    withRef stx do
    let oldFunCinfo ← getConstInfo oldFunName
    unless oldFunCinfo.hasValue do
      throwError "`mod_def` can only extend declarations defined with `def` or `theorem`"
    let unfoldEqn? ← getUnfoldEqnFor? oldFunName
    let extraMapNames ←
      if let some unfoldEqn := unfoldEqn? then
        auxDefs unfoldEqn oldFunName
      else
        auxDefs oldFunName
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut mapHeaders := #[]
    for oldAuxName in extraMapNames do
      let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
      mapHeaders := mapHeaders.push (← mkMappedDecl oldAuxName newAuxName)
    mapHeaders := mapHeaders.push (← mkMappedDecl oldFunName newFunName false)
    let decls := mapHeaders.map fun {newName, type, ..} => (newName,type)
    withLocalDeclsDND decls fun xs => do
      let add_temp_mappings := Id.run do
        let mut mappings := []
        for {cinfo, newName, isAux, type} in mapHeaders, x in xs do
          -- FVars cannot be universe-polymorphic. In particular, if the auxiliary declarations contained happen to not have the exact same universe levels as the original function, this whole thing breaks, with no easy way to fix it...
          assert! cinfo.levelParams = oldFunCinfo.levelParams
          let newMapEntry := {
            expr := x
            levelParams := []
            numArgs := 0
            numHoles := 0}
          mappings :=  (oldFunName.eraseMacroScopes,newMapEntry)::mappings
        return (.insertMany · mappings)
      -- mapped values are constructed in a temp map that contains the declarations being currently defined
      withModifyMap add_temp_mappings do
        let mut mvars := []
        let mut mappedValues := #[]
        let mut mappedTypes := #[]

        -- What follows from here is a horrible mess and should definitely be reworked to be more principled in the very near future..
        for {cinfo, newName, isAux, type} in mapHeaders do
          trace[Modular.Elab] "elaborating {newName}"
          let mut mappedValue ← modMapValueOrEqDef cinfo isAux
          let newMvars ← getMVarsNoDelayed mappedValue
          mvars := newMvars.toList ++ mvars
          mappedValues := mappedValues.push mappedValue
          let mappedType ← inferType mappedValue
          unless ← isDefEq mappedType type do
            throwError m!"Unexpected: mismatch between modmapped type and type of modmapped value : {type} ≠ {mappedType}"
          if mappedType.hasMVar then
            throwError "Type {mappedType} contains mvars, unfortunate. TODO addDecl while avoiding kernel check so this doesn't throw an error. We will discard this environment anyway as soon as the predefs are elabed."
          mappedTypes := mappedTypes.push mappedType

        trace[Modular.Elab] "Mapped values : {mappedValues}"
        let matchExtensions ← getMatchExtensions
        let matchMVars := matchExtensions.map MatchToExtend.mvar |> Std.HashSet.ofArray
        let matchClauses := match_clauses.getD #[] |>.map elabModularWhereMatch
        if matchExtensions.size != matchClauses.size then
          throwError "Expected {matchExtensions.size} match extensions, found {matchClauses.size} instead"
        -- TODO do context renaming using `argNames`
        for {matchName, mvar, originalMatch} in matchExtensions, {ref, name, alts, argNames} in matchClauses do
          withRef ref do
          let .str _ matchName := matchName | throwError "Unexpected match name {matchName}"
          unless Name.mkSimple matchName = name do
            throwErrorAt ref[0] "Unexpected user-provided match name: expected {matchName}, found {name}"
          -- Problem: right now, there is absolutely no guarantee that `originalMatch` is well-formed in the current context (namely, the fvars' types/values have been modmapped here already.), `matchExtensions` (and so `modMap`) should keep a copy of the original context during its traversal in order to reuse it here. Let's just pretend that's not an issue for now..
          mvar.withContext do
            trace[Modular.Elab] "originalMatch : {originalMatch}"
            let some matcherBundle ← mkMatcherBundle originalMatch | throwError "Expected matcher, found {originalMatch} instead"
            trace[Modular.Elab] "matcherBundle generated"
            let matcherBundle ← matcherBundle.modMap
            trace[Modular.Elab] "matcherBundle modmapped"
            trace[Modular.Elab] "patterns : {alts.map (·.patterns)}"
            let newMatcherExpr ← Term.withDeclName newFunName do matcherBundle.mkMatcher alts
            mvar.assign newMatcherExpr
        -- We solve mvars generated by extended matches separately
        mvars := mvars.filter (· ∉ matchMVars)
        trace[Modular.Elab] "Mvars : {mvars.map Expr.mvar}"

        if mvars.isEmpty  then
          if tacs matches some (some _) then
            throwError "Unexpected tactic block: the translation generated no obligations"
        else
          let some (some tac) := tacs
            | throwError "Missing `where ... finally` block to solve the missing holes"
          Term.withDeclName newFunName do solveGoalsWithTactic tac mvars
        trace[Modular.Elab] "Tactics elaborated"
        mappedValues.forM fun e => Meta.check e
        Term.synthesizeSyntheticMVarsNoPostponing
        mappedValues ← mappedValues.mapM instantiateMVars

        let declsConsts := mapHeaders.map fun {cinfo, newName, ..} => mkConst newName (cinfo.levelParams.map Level.param)
        mappedValues := mappedValues.map (·.replaceFVars xs declsConsts)
        if mappedValues.any Expr.hasExprMVar then
          throwError "`mod_def` generated unresolved metavariables"
        addDeclarationRangesFromSyntax newFunName newFun

        -- Once the mappedValues have been filled in correctly, we can safely construct the predefinitions
        let mut predefs : Array PreDefinition:= #[]
        for {cinfo, newName, isAux, ..} in mapHeaders, mappedValue in mappedValues, mappedType in mappedTypes do
          let predef := { ref := stx
                          kind := cinfo.kind!
                          levelParams := cinfo.levelParams
                          modifiers := modifiers
                          declName := newName
                          binders := .missing
                          type := mappedType
                          value := mappedValue
                          termination := if isAux then .none else termination_hint.rememberExtraParams 0 mappedValue}
          predefs := predefs.push predef
        trace[Modular.Elab] "Predefs : {predefs}"
        addPreDefinitions (← getLCtx, ← getLocalInstances) predefs
        trace[Modular.Elab] "Predefs elaborated successfully"
      -- All is done, we can leave the `withModifyMap` and `withLocalDeclsDND` scopes and add the correct mappings to the environment
    for {cinfo, newName, isAux, type} in mapHeaders do
        let newMapEntry := {
          expr := mkConst newName (cinfo.levelParams.map Level.param)
          levelParams := cinfo.levelParams
          numArgs := 0
          numHoles := 0}
        addMapEntry newName newMapEntry

  | _ => throwUnsupportedSyntax
