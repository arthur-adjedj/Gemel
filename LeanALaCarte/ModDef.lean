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
  cinfos : Array ConstantInfo
  newName : Name
  shortNewName : Name
  isAux : Bool
  type : Expr
deriving Inhabited

def mkMappedDecl (oldNames : Array Name) (newName : Name) (shortNewName : Name := newName) (isAux := true) (ref? : Option Syntax := none): ModularM MappedHeader := do
  let cinfos ← oldNames.mapM fun oldName => getConstInfo oldName
  let types ← cinfos.mapM fun cinfo => modMap cinfo.type
  -- If any of the modmapped types only gets partially mapped, we fail. We could potentially ask users to fill in those holes, or we may even consider merging types here in the future.
  if types.any Expr.hasMVar then
    throwError "ohno"
  if types[1:].any (types[0]! != · ) then
    throwError "terrible"
  return { ref?, cinfos, newName, shortNewName, isAux, type := types[0]! : MappedHeader}

def withMappedHeadersDecls {α} (decls : Array MappedHeader) (k : Array Expr → ModularM α) : ModularM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if h : i < decls.size then
      let header := decls[i]
      withAuxDecl header.newName header.type header.shortNewName fun fvar =>
        loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

def withMappedHeadersDeclss {α} (decls : Array (Array MappedHeader)) (k : Array (Array Expr) → ModularM α) : ModularM α :=
  let rec loop (i : Nat) (fvarss : Array (Array Expr)) := do
    if h : i < decls.size then
      let headers := decls[i]
      withMappedHeadersDecls headers fun fvars =>
        loop (i+1) (fvarss.push fvars)
    else
      k fvarss
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

instance : ToMessageData PreDefinition where
  toMessageData m :=
    m!"{m.declName} := {m.value} : {m.type}"

def modmapHeaders (mapHeaders : Array MappedHeader) : ModularM (List MVarId × Array Expr × Array Expr) := do
  let mut mvars := []
  let mut mappedValues := #[]
  let mut mappedTypes := #[]
  -- TODO merge modmapped values here
  for {cinfos , newName, isAux, type, ..} in mapHeaders do
    trace[Modular.Elab] "elaborating {newName}"
    let mut mappedValue ← modMapValueOrEqDefRhs cinfos[0]! isAux
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
  for {ref?, cinfos, newName, isAux, ..} in mapHeaders, mappedValue in mappedValues, mappedType in mappedTypes do
    let predef := { ref := if isAux then .missing else ref?.getD .missing
                    kind := cinfos[0]!.kind! --TODO ensure all cinfos have the same kind somewhere ?
                    levelParams := cinfos[0]!.levelParams
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

def modular_where_match_clause := leading_parser
  "matcher" >> Term.ident >> many Term.binderIdent >> "with " >> many (checkColGt >> Term.matchAlt)

syntax (name := modular_mod_def)
  declModifiers "mod" ws "def" ident "extends" (ident),+ ("where " colGe (ppLine modular_where_match_clause)* ("finally " tacticSeqIndentGt)? )?  Termination.suffix : modular_command

@[modular_elab modular_mod_def, incremental]
meta def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $decls:declModifiers mod def $newFunStx extends $[$oldFuns],* $[where $match_clauses* $[finally $tacs]?]?  $termination_stx) => liftModularM do withRef stx do
    let modifiers ← elabModifiers decls
    let modifiers := modifiers
    let termination_hint ← elabTerminationHints termination_stx
    let oldFunNames ← oldFuns.mapM fun oldFun => realizeGlobalConstNoOverloadWithInfo oldFun
    let oldFunCInfos ← oldFunNames.mapM getConstInfo
    unless oldFunCInfos.all (ConstantInfo.hasValue (allowOpaque := true)) do
      throwError "`mod def` can only extend declarations defined with `def` or `theorem`"
    unless oldFunCInfos[1:].all (oldFunCInfos[0]!.levelParams == ·.levelParams) do
      throwError
        "Functions getting extended do not all have the same universe level parameters" --TODO more accurate error message
    let expandedDeclId ← withRef? newFunStx do
      Term.expandDeclId (← getCurrNamespace) oldFunCInfos[0]!.levelParams newFunStx modifiers
    let newFunName := expandedDeclId.declName
    checkNotAlreadyDeclared newFunName
    let newShortName := expandedDeclId.shortName
    let extraMapNames ← oldFunNames.flatMapM fun oldFunName => do
      if let some e ← getEqDef? oldFunName then
        return (← e.auxDefs oldFunName) |>.map (oldFunName, ·) |>.toArray
      else
        return (← auxDefs oldFunName) |>.map (oldFunName, ·) |>.toArray
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut mapHeaders := #[]
    for (oldFunName,oldAuxName) in extraMapNames do
      let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
      -- We don't attempt to merge auxiliary defs for now, it might make sense to try to later
      mapHeaders := mapHeaders.push (← mkMappedDecl #[oldAuxName] newAuxName)
    let mainDeclHeader ← mkMappedDecl oldFunNames newFunName newShortName false
    mapHeaders := mapHeaders.push mainDeclHeader
    withMappedHeadersDecls mapHeaders fun xs => do
      let add_temp_mappings (map : ModularMap):= do
        let mut mappings := []
        for {cinfos, ..} in mapHeaders, x in xs do
          /- FVars cannot be universe-polymorphic. In particular, if the auxiliary declarations contained happen to not have the exact same universe levels as the original function, this whole thing breaks, with no easy way to fix it...
          The only culprit kind of auxiliary function I could find that does have more universes than the original declaration's is matchers. This is partly why they are abstracted away entirely in the modmapped term, and fresh matchers get elaborated in place of the original ones in `elabModMatch`.-/
          if let some errcinfo := cinfos.find? (·.levelParams != oldFunCInfos[0]!.levelParams) then
            throwError s!"Unexpected: Unable to abstract auxiliary function {errcinfo.name}: one of the original declarations has different level parameters ({errcinfo.levelParams}) compared to {oldFunCInfos[0]!.name} ({oldFunCInfos[0]!.levelParams})"
          let newMapEntry := {
            expr := x
            levelParams := []
            numArgs := 0
            numHoles := 0}
          mappings :=  cinfos.foldl (init := mappings) fun mappings cinfo => (cinfo.name,newMapEntry)::mappings
        return map.insertMany mappings
      -- mapped values are constructed in a temp map that contains the declarations being currently defined
      withSetMap (← add_temp_mappings (← getMap)) do
      withAssignableSyntheticOpaque do
        let lctx ← getLCtx
        let (mvars, mappedValues, mappedTypes) ← withReader (fun _ => lctx) do modmapHeaders mapHeaders
        trace[Modular.Elab] "Mapped values : {mappedValues}"
        let matchExtensions ← getMatchExtensions
        -- Some matches may have automatically been solved by unification thanks to `withAssignableSyntheticOpaque`
        let matchExtensions ← matchExtensions.toArray.filterM fun (mvar,_) => notM mvar.isAssigned
        -- Some matches may need to be translated while not really needing new matches, e.g consider a match matching on `List A` in a context mapping `A` to `B`.
        for (mvar,matchExt) in matchExtensions do
            try
              withTraceNode `Modular.Elab (fun _ => return s!"Trying to Elaborate matcher {matchExt.map (·.matchName)} without adding new branches") do
                elabModMatchNoClauses newFunName mvar matchExt
                trace[Modular.Elab] "Elaboration of matcher {matchExt.map (·.matchName)} succeeded without adding new branches"
            catch | _ => continue
        let matchExtensions ← matchExtensions.filterM fun (mvar,_) => notM mvar.isAssigned
        let matchClauses := match_clauses.getD #[] |>.map elabModularWhereMatch
        if matchExtensions.size != matchClauses.size then
          throwError "Expected {matchExtensions.size} match extensions, found {matchClauses.size} instead"
        for (mvar,matchExt) in matchExtensions, matchClause in matchClauses do
          elabModMatch newFunName mvar matchExt matchClause
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
        let declsConsts := mapHeaders.map fun {cinfos, newName, ..} => mkConst newName (cinfos[0]!.levelParams.map Level.param)
        mappedValues := mappedValues.map (·.replaceFVars xs declsConsts)
        if mappedValues.any Expr.hasExprMVar then
          throwError "`mod def` generated unresolved metavariables"
        addDeclarationRangesFromSyntax newFunName stx
        -- Once the mappedValues have been filled in correctly, we can safely construct the predefinitions
        addPreDefs modifiers termination_hint mapHeaders mappedValues mappedTypes
        addConstInfo newFunStx newFunName mainDeclHeader.type
    -- All is done, we can leave the `withMappedHeadersDecls` and `withSetMap` scopes and add the correct mappings to the environment
    for {cinfos, newName, ..} in mapHeaders do
      let newMapEntry := {
        expr := mkConst newName (cinfos[0]!.levelParams.map Level.param)
        levelParams := cinfos[0]!.levelParams
        numArgs := 0
        numHoles := 0}
      cinfos.forM fun cinfo => do
        addMapEntry cinfo.name newMapEntry
        addUnfoldEqMapping cinfo.name newName
        addEqnMappings cinfo.name newName
  | _ => throwUnsupportedSyntax
