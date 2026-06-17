module

public meta import Lean.Elab.PreDefinition.Main
public meta import LeanALaCarte.CollectAuxDefs
public meta import Lean.Meta.Tactic.Try.Collect
public import LeanALaCarte.AuxMapping
public import LeanALaCarte.ExtendMatch
public meta import Std.Do.Triple.SpecLemmas
import Lean.Elab.PreDefinition.Basic

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
  let fallback _ := modMap (cinfo.value! (allowOpaque := true))
  if isAux then fallback ()
  else
    let some value ← getEqDef? cinfo.name | fallback ()
    modMap value

def solveGoalsWithTactic (tac : Syntax) (goals : List MVarId) : TermElabM Unit := do
  let goals ← goals.filterM fun mvar => mvar.isAssignable
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
  ref? : Option Syntax
  cinfo : ConstantInfo
  newName : Name
  shortNewName : Name
  isAux : Bool
  type : Expr
deriving Inhabited

def mkMappedDecl (oldName newName : Name) (shortNewName : Name := newName) (isAux := true) (ref? : Option Syntax := none): ModularM MappedHeader := do
  let cinfo ← getConstInfo oldName
  let type ← modMap cinfo.type
  assert! !type.hasMVar
  return { ref?, cinfo, newName, shortNewName, isAux, type }

def withMappedHeadersDecls {α} (decls : Array MappedHeader) (k : Array Expr → ModularM α) : ModularM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < decls.size then
      let header := decls[i]
      withAuxDecl header.newName header.type header.shortNewName fun fvar =>
        loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

def addUnfoldEqMapping (oldName newName : Name) : ModularM Unit := do
  let some oldEqn ← getUnfoldEqnFor? oldName true | return
  let some newEqn ← getUnfoldEqnFor? newName true | return
  trace[Modular.Elab] "oldEqns : {oldEqn}"
  trace[Modular.Elab] "newEqns : {newEqn}"
  addAuxMapping oldEqn newEqn

def addEqnMappings (oldName newName : Name) : ModularM Unit := do
  let some oldEqns ← getEqnsFor? oldName | return
  let some newEqns ← getEqnsFor? newName | return
  trace[Modular.Elab] "oldEqns : {oldEqns}"
  trace[Modular.Elab] "newEqns : {newEqns}"
  for oldEqn in oldEqns, newEqn in newEqns do
    addAuxMapping oldEqn newEqn


def modular_where_match_clause := leading_parser
  "matcher" >> Term.ident >> many Term.binderIdent >> "with " >> many (checkColGt >> Term.matchAlt)

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

syntax (name := modular_mod_def)
  declModifiers "mod" ws "def" (ident)? "extends" ident ("where " colGe (ppLine modular_where_match_clause)* ("finally " tacticSeqIndentGt)? )?  Termination.suffix : modular_command

instance : ToMessageData PreDefinition where
  toMessageData m :=
    m!"{m.declName} := {m.value} : {m.type}"

def withArgNames (argNames : Array Name) (k : ModularM α): ModularM α := do
  let mut lctx ← getLCtx
  let hyps ← getLocalHyps
  for argName in argNames, hyp in hyps do
    lctx := lctx.setUserName hyp.fvarId! argName
  withTheReader Meta.Context (fun s => {s with lctx := lctx})
    k

def modmapHeaders (mapHeaders : Array MappedHeader) : ModularM (List MVarId × Array Expr × Array Expr) := do
  let mut mvars := []
  let mut mappedValues := #[]
  let mut mappedTypes := #[]
  for {cinfo, newName, isAux, type, ..} in mapHeaders do
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
  return (mvars, mappedValues, mappedTypes)

def addPreDefs (modifiers : Modifiers) (termination_hint : TerminationHints) (mapHeaders : Array MappedHeader) (mappedValues mappedTypes : Array Expr): ModularM Unit := do
  let mut predefs : Array PreDefinition:= #[]
  for {ref?, cinfo, newName, isAux, ..} in mapHeaders, mappedValue in mappedValues, mappedType in mappedTypes do
    let predef := { ref := if isAux then .missing else ref?.getD .missing
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

def elabModMatch (newFunName : Name) (matchExt : MatchToExtend) (matchClause : MatchClause) : ModularM Unit := do
  let {matchName, mvar, originalMatch, modMappedRhss, originalLCtx} := matchExt
  let {ref, name, alts, argNames} := matchClause
  if ← mvar.isAssigned then return
  withRef ref do
  trace[Modular.Elab] "Elaborating matcher : {name} {Expr.mvar mvar}"
  let .str _ matchName := matchName | throwError "Unexpected match name {matchName}"
  unless Name.mkSimple matchName = name do
    throwErrorAt ref[0] "Unexpected user-provided match name: expected {matchName}, found {name}"
  let mvarDecl ← mvar.getDecl
  withLCtx' originalLCtx do
  withSetModMappedLCtx mvarDecl.lctx do
    trace[Modular.Elab] "originalMatch : {originalMatch}"
    trace[Modular.Elab] "modMappedRhss : {modMappedRhss}"
    let some matcherBundle ← mkMatcherBundle originalMatch | throwError "Expected matcher, found {originalMatch} instead"
    trace[Modular.Elab] "matcherBundle generated"
    let matcherBundle ← matcherBundle.modMap modMappedRhss
    trace[Modular.Elab] "matcherBundle modmapped"
    trace[Modular.Elab] "patterns : {alts.map (·.patterns)}"
    withModMappedLCtx do
    withArgNames argNames do
    Term.withDeclName newFunName do
      let newMatcherExpr ← matcherBundle.mkMatcher alts
      mvar.assign newMatcherExpr

def elabModMatchNoClauses (newFunName : Name) (matchExt : MatchToExtend) : ModularM Unit := do
  let .str _ name := matchExt.matchName | throwError "Unexpected match name {matchExt.matchName}"
  elabModMatch newFunName matchExt ⟨.missing, .mkSimple name,#[],#[]⟩

@[modular_elab modular_mod_def, incremental]
meta def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $decls:declModifiers mod def $[$newFunStx?]? extends $oldFun $[where $match_clauses* $[finally $tacs]?]?  $termination_stx) => liftModularM do withRef stx do
    let modifiers ← elabModifiers decls
    let modifiers := modifiers
    let termination_hint ← elabTerminationHints termination_stx
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun
    let oldFunCinfo ← getConstInfo oldFunName
    unless oldFunCinfo.hasValue (allowOpaque := true) do
      throwError "`mod def` can only extend declarations defined with `def` or `theorem`"
    let expandedDeclId ← withRef? newFunStx? do
      let newFunStx :=
        if let some newFunStx := newFunStx? then
          newFunStx else
        if let .str _ oldFunSuffix := oldFunName then mkIdent (.mkSimple oldFunSuffix) else oldFun
      Term.expandDeclId (← getCurrNamespace) oldFunCinfo.levelParams newFunStx modifiers
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
    let mainDeclHeader ← mkMappedDecl oldFunName newFunName newShortName false
    mapHeaders := mapHeaders.push mainDeclHeader
    withMappedHeadersDecls mapHeaders fun xs => do
      let add_temp_mappings (map : ModularMap):= do
        let mut mappings := []
        for {cinfo, ..} in mapHeaders, x in xs do
          /- FVars cannot be universe-polymorphic. In particular, if the auxiliary declarations contained happen to not have the exact same universe levels as the original function, this whole thing breaks, with no easy way to fix it...
          The only culprit kind of auxiliary function I could find that does have more universes than the original declaration's is matchers. This is partly why they are abstracted away entirely in the modmapped term, and fresh matchers get elaborated in place of the original ones in `elabModMatch`.-/
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
      withAssignableSyntheticOpaque do
        let lctx ← getLCtx
        let (mvars, mappedValues, mappedTypes) ← withReader (fun _ => lctx) do modmapHeaders mapHeaders
        trace[Modular.Elab] "Mapped values : {mappedValues}"
        let matchExtensions ← getMatchExtensions
        -- Some matches may have automatically been solved by unification thanks to `withAssignableSyntheticOpaque`
        let matchExtensions ← matchExtensions.valuesArray.filterM fun {mvar,..} => notM mvar.isAssigned
        -- Some matches may need to be translated while not really needing new matches, e.g consider a match matching on `List A` in a context mapping `A` to `B`.
        for matchExt in matchExtensions do
            try
              withTraceNode `Modular.Elab (fun _ => return s!"Trying to Elaborate matcher {matchExt.matchName} without adding new branches") do
                elabModMatchNoClauses newFunName matchExt
                trace[Modular.Elab] "Elaboration of matcher {matchExt.matchName} succeeded without adding new branches"
            catch | _ => continue
        let matchExtensions ← matchExtensions.filterM fun {mvar,..} => notM mvar.isAssigned
        let matchClauses := match_clauses.getD #[] |>.map elabModularWhereMatch
        if matchExtensions.size != matchClauses.size then
          throwError "Expected {matchExtensions.size} match extensions, found {matchClauses.size} instead"
        for matchExt in matchExtensions, matchClause in matchClauses do
          elabModMatch newFunName matchExt matchClause
        -- We solve mvars generated by extended matches separately
        let mvars ← mvars.mapM getDelayedMVarRoot
        let mvars ← mvars.filterM (notM ·.isAssigned)
        trace[Modular.Elab] "Mvars filtered : {mvars.map Expr.mvar}"

        if mvars.isEmpty  then
          if let some (some tac) := tacs then
            throwErrorAt tac "Unexpected tactic block: the translation generated no obligations"
        else
          let some (some tac) := tacs
            | throwError "Missing `where ... finally` block to solve the missing holes"
          Term.withDeclName newFunName do solveGoalsWithTactic tac mvars
        trace[Modular.Elab] "Tactics elaborated"
        mappedValues.forM fun e => Meta.check e
        Term.synthesizeSyntheticMVarsNoPostponing
        let mut mappedValues ← mappedValues.mapM instantiateMVars
        trace[Modular.Elab] "mapped values after instantiation: {mappedValues}"
        let declsConsts := mapHeaders.map fun {cinfo, newName, ..} => mkConst newName (cinfo.levelParams.map Level.param)
        mappedValues := mappedValues.map (·.replaceFVars xs declsConsts)
        if mappedValues.any Expr.hasExprMVar then
          throwError "`mod def` generated unresolved metavariables"
        addDeclarationRangesFromSyntax newFunName stx
        -- Once the mappedValues have been filled in correctly, we can safely construct the predefinitions
        addPreDefs modifiers termination_hint mapHeaders mappedValues mappedTypes
        if let some newFunInfo := newFunStx? then
          addConstInfo newFunInfo newFunName mainDeclHeader.type
    -- All is done, we can leave the `withMappedHeadersDecls` and `withSetMap` scopes and add the correct mappings to the environment
    for {cinfo, newName, ..} in mapHeaders do
      let newMapEntry := {
        expr := mkConst newName (cinfo.levelParams.map Level.param)
        levelParams := cinfo.levelParams
        numArgs := 0
        numHoles := 0}
      addMapEntry cinfo.name newMapEntry
      addUnfoldEqMapping cinfo.name newName
      addEqnMappings cinfo.name newName
  | _ => throwUnsupportedSyntax
