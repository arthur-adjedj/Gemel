module

public meta import Lean.Elab.PreDefinition.Main
public meta import LeanALaCarte.CollectAuxDefs
public meta import Lean.Meta.Tactic.Try.Collect
public import LeanALaCarte.AuxMapping
public import LeanALaCarte.ExtendMatch
public meta import Std.Do.Triple.SpecLemmas

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
    throwError "ohno, this is bad!"
  if types[1:].any (types[0]! != · ) then
    throwError "terrible"
  return { ref?, cinfos, newName, shortNewName, isAux, type := types[0]! : MappedHeader}

def withMappedHeadersDecls {α} (oldFunCInfo : ConstantInfo) (decls : Array MappedHeader) (k : Array Expr → ModularM α) : ModularM α :=
  let rec loop (i : Nat) (fvars : Array Expr) := do
    if _ : i < decls.size then
      let {cinfos, newName, type, shortNewName ,..} := decls[i]
      withAuxDecl newName type shortNewName fun fvar => do
        if let some errcinfo := cinfos.find? (·.levelParams != oldFunCInfo.levelParams) then
          throwError s!"Internal error: Unable to abstract auxiliary function {errcinfo.name}: one of the original declarations has different level parameters ({errcinfo.levelParams}) compared to {oldFunCInfo.name} ({oldFunCInfo.levelParams})"
        let newMapEntry := {
          expr := fvar
          levelParams := []
          numArgs := 0
          numHoles := 0}
        cinfos.foldl (init := loop (i+1) (fvars.push fvar))
          fun k cinfo => withModifyMap (·.insert cinfo.name newMapEntry) k
    else
      k fvars
  loop 0 #[]

instance : ToMessageData PreDefinition where
  toMessageData m :=
    m!"{m.declName} := {m.value} : {m.type}"

def modmapHeaders (mapHeaders : Array MappedHeader) : ModularM (List MVarId × Array Expr × Array Expr) := do
  let mut mvars := []
  let mut mappedValues := #[]
  let mut mappedTypes := #[]
  for {cinfos , newName, isAux, type, ..} in mapHeaders do
    trace[Modular.Elab] "elaborating {newName}"
    trace[Modular.Elab] "Modmapping values of {cinfos.map (·.name)}"
    let tempMappedValues ← cinfos.mapM fun cinfo => modMapValueOrEqDefRhs cinfo isAux
    trace[Modular.Elab] "mapped values {tempMappedValues}"
    let mappedValue ← mergeExprs tempMappedValues
    trace[Modular.Elab] "merged value {mappedValue}"
    let newMvars ← getMVarsNoDelayed mappedValue
    mvars := newMvars.toList ++ mvars
    mappedValues := mappedValues.push mappedValue
    let mappedType ← inferType mappedValue
    unless ← isDefEq mappedType type do
      throwError m!"Internal error: mismatch between modmapped type and type of modmapped value : {type} ≠ {mappedType}"
    if mappedType.hasMVar then
      throwError "Type {mappedType} contains mvars, unfortunate. TODO addDecl while avoiding kernel check so this doesn't throw an error. We will discard this environment anyway as soon as the predefs are elabed."
    mappedTypes := mappedTypes.push type
  return (mvars, mappedValues, mappedTypes)

def addPreDefs (modifiers : Modifiers) (termination_hint : TerminationHints) (mapHeaders : Array MappedHeader) (mappedValues mappedTypes : Array Expr): ModularM Unit := do
  let mut predefs : Array PreDefinition:= #[]
  for {ref?, cinfos, newName, isAux, ..} in mapHeaders, mappedValue in mappedValues, mappedType in mappedTypes do
    let predef := { ref := if isAux then .missing else ref?.getD .missing
                    kind := cinfos[0]!.kind! --TODO ensure all cinfos have the same kind somewhere ?
                    levelParams := cinfos[0]!.levelParams
                    modifiers := if isAux then default else modifiers
                    declName := newName
                    binders := .missing
                    type := mappedType
                    value := mappedValue
                    termination := if isAux then .none else termination_hint.rememberExtraParams 0 mappedValue}
    predefs := predefs.push predef
  trace[Modular.Elab] "Predefs : {predefs}"
  addPreDefinitions (← getLCtx, ← getLocalInstances) predefs
  trace[Modular.Elab] "Predefs elaborated successfully"

def addFinalMappings (stx : Syntax) (mapHeaders : Array MappedHeader) : ModularM Unit := do
  for {cinfos, newName, ..} in mapHeaders do
    addDeclarationRangesFromSyntax newName stx
    let newMapEntry := {
      expr := mkConst newName (cinfos[0]!.levelParams.map Level.param)
      levelParams := cinfos[0]!.levelParams
      numArgs := 0
      numHoles := 0}
    cinfos.forM fun cinfo => do
      addMapEntry cinfo.name newMapEntry
      addUnfoldEqMapping cinfo.name newName
      addEqnMappings cinfo.name newName

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
    let expandedDeclId ← Term.expandDeclId (← getCurrNamespace) oldFunCInfos[0]!.levelParams newFunStx modifiers
    let newFunName := expandedDeclId.declName
    Lean.Elab.Term.withDeclName' newFunName do
    checkNotAlreadyDeclared newFunName
    let newShortName := expandedDeclId.shortName
    let extraMapNames ← oldFunNames.flatMapM fun oldFunName => do
      if let some e ← getEqDef? oldFunName then
        return (← e.auxDefs oldFunName) |>.map (oldFunName, ·) |>.toArray
      else
        return (← auxDefs oldFunName) |>.map (oldFunName, ·) |>.toArray
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut mapHeaders := #[]
    for (oldFunName, oldAuxName) in extraMapNames do
      --We must ensure there are no naming conflicts between auxiliary name functions
      --eg consider `mod def foo extends A.foo, B.foo` where both `A.foo._proof_1` and `B.foo._proof_1` exist (and are incompatible)
      let newAuxNameSuffix := oldAuxName.replacePrefix oldFunName .anonymous
      trace[Modular.Elab] "prefix: {newAuxNameSuffix}"
      let newAuxName ← mkAuxDeclName newAuxNameSuffix
      -- This is hacky. Instead, the decl header should be already added to the env here st `mkAuxDeclName` can handle conflicts by itself, TODO: better
      setDeclNGen (← getDeclNGen).next
      trace[Modular.Elab] "newAuxName: {newAuxName}"
      -- We don't attempt to merge auxiliary defs for now, it might make sense to try to later
      mapHeaders := mapHeaders.push (← mkMappedDecl #[oldAuxName] newAuxName)
    let mainDeclHeader ← mkMappedDecl oldFunNames newFunName newShortName false
    mapHeaders := mapHeaders.push mainDeclHeader
    trace[Modular.Elab] "Functions to be elaborated: {mapHeaders.map MappedHeader.newName}"
    withMappedHeadersDecls oldFunCInfos[0]! mapHeaders fun xs => do
      withAssignableSyntheticOpaque do
      let (mvars, mappedValues, mappedTypes) ← withSetModMappedLCtx (← getLCtx) do modmapHeaders mapHeaders
      trace[Modular.Elab] "Mapped values : {mappedValues}"
      let matchExtensions ← getMatchExtensions
      -- Some matches may have automatically been solved by unification thanks to `withAssignableSyntheticOpaque`
      let matchExtensions ← matchExtensions.toArray.filterM fun (mvar,_) => notM mvar.isAssigned
      -- Some matches may need to be translated while not really needing new matches, e.g consider a match on `List A` in a context mapping `A` to `B`.
      for (mvar,matchExt) in matchExtensions do
        try
          withTraceNode `Modular.Elab (fun | .ok _ => return m!"Successfully elaborated matcher {← matchExt.mapM fun m => mkConstWithLevelParams m.matchName} without adding new branches !"
                                           | .error e => return m!"Failed to elaborate matcher {← matchExt.mapM fun m => mkConstWithLevelParams m.matchName} without adding new branches: \n{e.toMessageData}") do
            elabModMatchNoClauses mvar matchExt
            trace[Modular.Elab] "Elaboration of matcher {matchExt.map (·.matchName)} succeeded without adding new branches"
        catch | _ => continue
      let matchExtensions ← matchExtensions.filterM fun (mvar,_) => notM mvar.isAssigned
      let matchClauses := match_clauses.getD #[] |>.map elabModularWhereMatch
      if matchExtensions.size != matchClauses.size then
        throwError "Expected {matchExtensions.size} match extensions, found {matchClauses.size} instead"
      for (mvar,matchExt) in matchExtensions, matchClause in matchClauses do
        elabModMatch mvar matchExt matchClause
      -- We solve mvars generated by extended matches separately
      -- let mvars ← mvars.mapM getDelayedMVarRoot
      let mvars ← mvars.filterM (notM ·.isAssigned)
      trace[Modular.Elab] "Mvars filtered : {mvars.map Expr.mvar}"

      if mvars.isEmpty then
        if let some (some tac) := tacs then
          throwErrorAt tac "Unexpected tactic block: the translation generated no obligations"
      else
        let some (some tac) := tacs
          | throwError "Missing `where ... finally` block to solve the missing holes"
        solveGoalsWithTactic tac mvars
      trace[Modular.Elab] "Tactics elaborated"
      mappedValues.forM fun e => Meta.check e
      Term.synthesizeSyntheticMVarsNoPostponing
      let mut mappedValues ← mappedValues.mapM instantiateMVars
      trace[Modular.Elab] "mapped values after instantiation: {mappedValues}"
      let declsConsts := mapHeaders.map fun {cinfos, newName, ..} => mkConst newName (cinfos[0]!.levelParams.map Level.param)
      mappedValues := mappedValues.map (·.replaceFVars xs declsConsts)
      if mappedValues.any Expr.hasExprMVar then
        throwError "Internal error: `mod def` generated unresolved metavariables"
      -- Once the mappedValues have been filled in correctly, we can safely construct the predefinitions
      addPreDefs modifiers termination_hint mapHeaders mappedValues mappedTypes
      addConstInfo newFunStx newFunName mainDeclHeader.type
    -- All is done, we can leave the `withMappedHeadersDecls` scopes and add the correct mappings to the environment
    addFinalMappings stx mapHeaders
  | _ => throwUnsupportedSyntax
