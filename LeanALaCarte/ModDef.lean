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

def modMapValueOrEqDefRhs (cinfo : ConstantInfo) (isAux : Bool) : ModularM Expr := do
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
  shortNewName : Name
  isAux : Bool
  type : Expr
deriving Inhabited

def mkMappedDecl (oldName newName : Name) (shortNewName : Name := newName) (isAux := true): ModularM MappedHeader := do
  let cinfo ← getConstInfo oldName
  let type ← modMap cinfo.type
  assert! !type.hasMVar
  return { cinfo, newName, shortNewName, isAux, type }

def withMappedHeadersDecls {α} (decls : Array MappedHeader) (k : Array Expr → ModularM α) : ModularM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < decls.size then
      let header := decls[i]
      withAuxDecl header.newName header.type header.shortNewName fun fvar => loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

def modular_where_match_clause := leading_parser
  "matcher" >> Term.ident >> many Term.binderIdent >> "with " >> checkColGt >> many Term.matchAlt

structure MatchClause where
  ref  : Syntax
  name : Name
  argNames : Array Name --TODO use that to rename context vars
  alts : Array Term.TermMatchAltView

def elabModularWhereMatch (stx : Syntax) : MatchClause :=
  let name := stx[1].getId
  let argNames := stx[2].getArgs.map Syntax.getId
  let alts := stx[4].getArgs.filterMap (Term.getMatchAlt `term)
  { ref := stx, name, argNames, alts }

syntax (name := modular_mod_def)
  declModifiers "mod_def" (ident)? "extends" ident ("where " colGt (ppLine modular_where_match_clause)* ("finally " tacticSeqIndentGt)? )?  Termination.suffix : modular_command

instance : ToMessageData PreDefinition where
  toMessageData m :=
    m!"{m.declName} := {m.value} : {m.type}"

@[modular_elab modular_mod_def, incremental]
meta def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $mod:declModifiers mod_def $[$newFun]? extends $oldFun $[where $match_clauses* $[finally $tacs]?]?  $termination_stx) => liftModularM do withRef stx do
    let modifiers ← elabModifiers mod
    let modifiers := modifiers
    let termination_hint ← elabTerminationHints termination_stx
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun

    withRef stx do
    let oldFunCinfo ← getConstInfo oldFunName
    unless oldFunCinfo.hasValue do
      throwError "`mod_def` can only extend declarations defined with `def` or `theorem`"
    let expandedDeclId ← withRef? newFun do
      Term.expandDeclId (← getCurrNamespace) oldFunCinfo.levelParams (newFun.getD oldFun) modifiers
    let newFunName := expandedDeclId.declName
    checkNotAlreadyDeclared newFunName
    let newShortName := expandedDeclId.shortName
    let extraMapNames ←
      if let some e ← getEqDef? oldFunName then
        e.auxDefs oldFunName
      else
        auxDefs oldFunName
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut mapHeaders := #[]
    for oldAuxName in extraMapNames do
      let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
      mapHeaders := mapHeaders.push (← mkMappedDecl oldAuxName newAuxName)
    mapHeaders := mapHeaders.push (← mkMappedDecl oldFunName newFunName newShortName false)
    withMappedHeadersDecls mapHeaders fun xs => do
      let add_temp_mappings (map : ModularMap):= do
        let mut mappings := []
        for {cinfo, newName, shortNewName, isAux, type} in mapHeaders, x in xs do
          -- FVars cannot be universe-polymorphic. In particular, if the auxiliary declarations contained happen to not have the exact same universe levels as the original function, this whole thing breaks, with no easy way to fix it...
          unless cinfo.levelParams = oldFunCinfo.levelParams do
            throwError s!"Unexpected: Unable to abstract auxiliary function {cinfo.name}: the original declaration has different level parameters ({cinfo.levelParams}) compared to {oldFunCinfo.name} (oldFunCinfo.levelParams)"
          let newMapEntry := {
            expr := x
            levelParams := []
            numArgs := 0
            numHoles := 0}
          mappings :=  (oldFunName,newMapEntry)::mappings
        return map.insertMany mappings
      -- mapped values are constructed in a temp map that contains the declarations being currently defined
      withSetMap (← add_temp_mappings (← getMap)) do
        let mut mvars := []
        let mut mappedValues := #[]
        let mut mappedTypes := #[]

        for {cinfo, newName, shortNewName, isAux, type} in mapHeaders do
          trace[Modular.Elab] "elaborating {newName}"
          let mut mappedValue ← modMapValueOrEqDefRhs cinfo isAux
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
          trace[Modular.Elab] "Elaborating matcher : {name}"
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
        newFun.forM (fun name => addDeclarationRangesFromSyntax newFunName name)

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
    for {cinfo, newName, shortNewName, isAux, type} in mapHeaders do
      let newMapEntry := {
        expr := mkConst newName (cinfo.levelParams.map Level.param)
        levelParams := cinfo.levelParams
        numArgs := 0
        numHoles := 0}
      addMapEntry cinfo.name newMapEntry
      -- TODO also add entry for `.eq_def` ?
      let some oldEqns ← getEqnsFor? cinfo.name | continue
      let some newEqns ← getEqnsFor? newName    | continue
      trace[Modular.Elab] "oldEqns : {oldEqns}"
      trace[Modular.Elab] "newEqns : {newEqns}"
      for oldEqn in oldEqns, newEqn in newEqns do
        addAuxMapping oldEqn newEqn


  | _ => throwUnsupportedSyntax
