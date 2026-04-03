import Lean.Parser.Command
import Lean.Parser.Tactic
import Lean.Elab.MutualDef
import Lean.Meta.Tactic.Try
import LeanALaCarte.ModMap
import LeanALaCarte.Elab
import LeanALaCarte.CollectDelayedAssignementsWithArgs
import LeanALaCarte.AuxMapping
import LeanALaCarte.CollectAuxDefs
import LeanALaCarte.UnfoldEqns

open Lean Parser Elab Meta Command

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
  let map ← get
  let fallback _ := modMap map cinfo.value!
  if isAux then fallback ()
  else
    let some value ← getEqDef? cinfo.name | fallback ()
    modMap map value

private partial def solveGoalsWithTactic (tac : Syntax) (goals : List MVarId) : TermElabM Unit := do
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

def withReplaceMVarsWithFVars [Inhabited α] (e: Expr) (k : Expr → Array Expr → MetaM α) : MetaM α := do
  let delayedMvarsWithArgs ← e.collectDelayedAssignmentsWithArgs
  let mvarsWithAppTy ← delayedMvarsWithArgs.mapM fun e => do
    let mvar := e.getAppFn.mvarId!
    mvar.withContext do
      let mvarTy ← mvar.getType
      let args := e.getAppArgs
      forallBoundedTelescope mvarTy args.size fun xs ty => return ty.replaceFVars xs args
  trace[Modular.Elab] "delayedMvarsWithArgs : {delayedMvarsWithArgs}"
  trace[Modular.Elab] "mvarsWithAppTy : {mvarsWithAppTy}"
  let decls ← mvarsWithAppTy.mapM fun ty => do return (← mkFreshId,ty)
  withLocalDeclsDND decls fun xs => do
  trace[Modular.Elab] "new fvars : {xs}"
  let e := e.replace fun t =>
    -- TODO once the TODO in `collectDelayedAssignmentsWithArgs` is done, use `ptrEq` rather than `==` here
    delayedMvarsWithArgs.findIdx? (t == ·) |>.map fun idx => xs[idx]!
  -- trace[Modular.Elab] "new term : {e}"
  Meta.check e
  k e xs

structure MappedHeader where
  cinfo : ConstantInfo
  newName : Name
  isAux : Bool
  type : Expr
deriving Inhabited

def mkMappedDecl (oldName newName : Name) (isAux := true): ModularM MappedHeader := do
  let cinfo ← getConstInfo oldName
  let type ← modMap (← get) cinfo.type
  assert! !type.hasMVar
  return { cinfo, newName, isAux, type }


private def collectExprConstants (exprs : Array Expr) : NameSet :=
  exprs.foldl (init := {}) fun names e => e.foldConsts names fun c cs => cs.insert c

--AI Slop that works, TODO review
private def collectRetainedDecls (envBefore : Environment) (tempAxiomNames : NameSet)
    (roots : NameSet) : TermElabM (Std.HashMap Name ConstantInfo) := do
  profileitM Exception s!"collectRetainedDecls" (← getOptions) do
    let envAfter ← getEnv
    let mut retained : Std.HashMap Name ConstantInfo := {}
    let mut seen : NameSet := {}
    let mut worklist : List Name := roots.toList
    while !worklist.isEmpty do
      let name := worklist.head!
      worklist := worklist.tail!
      if seen.contains name then
        continue
      seen := seen.insert name
      if envBefore.contains name || tempAxiomNames.contains name then
        continue
      let some cinfo := envAfter.find? name
        | continue
      retained := retained.insert name cinfo
      for depName in cinfo.getUsedConstantsAsSet do
        if !tempAxiomNames.contains depName && !seen.contains depName then
          worklist := depName :: worklist
    return retained

private structure TopoRetainedState where
  visiting : NameSet := {}
  visited : NameSet := {}
  ordered : Array ConstantInfo := #[]

--AI Slop that works, TODO review
private partial def topoSortRetainedDeclsVisit
    (declMap : Std.HashMap Name ConstantInfo)
    (name : Name) : StateRefT TopoRetainedState TermElabM Unit := do
  let s ← get
  if s.visited.contains name then
    return
  if s.visiting.contains name then
    throwError "cycle detected while ordering generated auxiliary declarations at `{name}`"
  let some cinfo := declMap.get? name
    | return
  modify fun s => { s with visiting := s.visiting.insert name }
  for depName in ConstantInfo.getUsedConstantsAsSet cinfo do
    if declMap.contains depName then
      topoSortRetainedDeclsVisit declMap depName
  modify fun s =>
    { s with
      visiting := s.visiting.erase name
      visited := s.visited.insert name
      ordered := s.ordered.push cinfo }

--AI Slop that works, TODO review
private def topoSortRetainedDecls (declMap : Std.HashMap Name ConstantInfo) : TermElabM (Array ConstantInfo) := do
  profileitM Exception s!"topoSortRetainedDecls" (← getOptions) do
    let (_, s) ← (do
      for name in declMap.keys do
        topoSortRetainedDeclsVisit declMap name
    : StateRefT TopoRetainedState TermElabM Unit) |>.run {}
    return s.ordered

/-- Turn a `ConstantInfo` into a declaration. Stolen from mathlib -/
def Lean.ConstantInfo.toDeclaration! : ConstantInfo → Declaration
  | .defnInfo   info => Declaration.defnDecl info
  | .thmInfo    info => Declaration.thmDecl     info
  | .axiomInfo  info => Declaration.axiomDecl   info
  | .opaqueInfo info => Declaration.opaqueDecl  info
  | .quotInfo   _ => panic! "toDeclaration for quotInfo not implemented"
  | .inductInfo _ => panic! "toDeclaration for inductInfo not implemented"
  | .ctorInfo   _ => panic! "toDeclaration for ctorInfo not implemented"
  | .recInfo    _ => panic! "toDeclaration for recInfo not implemented"

private def replayRetainedDecls (decls : Array ConstantInfo) : TermElabM Unit := do
profileitM Exception s!"replayRetainedDecls" (← getOptions) do
  for cinfo in decls do
    addDecl cinfo.toDeclaration!

/- TODO adapt syntax to take into account:
- docstrings
- attributes
- termination hints
- `where` clauses
- (maybe ?) make the current `by` goals be filled in as holes in `where finally` ? (this would be non-trivial in cases where the holes appear in auxiliary defs rather than the "real" one. One solution could be to inline/delta-reduce auxiliary defs that aren't matchers, and translating the core def directly, leaving the job of re-abstracting relevant parts of the code to the usual elaborator for `PreDef`s. The big danger to doing that is obviously performance. `modMap`ed terms need to be `check`ed to instantiate the type of the introduced mvars for now, and doing so on terms containing very large proof terms (e.g `grind` or `omega` proofs) is bound to be expensive. A solution would be to get rid of `Meta.check` in `modMap`, but I'm confident type-checking is still called a fair few times when elaborating PreDefs, so this doesn't solve the issue of abstracting the proofs at the right time.)

Once that is all done, translate that syntax to a `DefView` and elaborate it like any other function, making use of all the niceties the lean elaborator offers :D
Actually, `DefView` contain the value as a syntax, not as an Expr, this is not ideal because it implies needing to first delaborate the translated term before re-elaborating it.. Let's try to translate things directly to `PreDef`s instead, this will be a bit of a PITA...
-/

syntax (name := modular_mod_def)
  declModifiers "mod_def" ident "extends" ident (ppDedent(ppLine) "where" ppDedent(ppLine) tacticSeqIndentGt)?  Termination.suffix : modular_command

@[modular_elab modular_mod_def, incremental]
def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $mod:declModifiers mod_def $newFun extends $oldFun $[where $tacs]? $termination_stx) => liftModularM do
    let modifiers ← elabModifiers mod
    let modifiers := {modifiers with computeKind := .noncomputable} -- For now, generated expressions contain `.brecOns` often, which the lean compiler doesn't currently handle.
    let termination_hint ← elabTerminationHints termination_stx
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun
    let newFunName := (← getCurrNamespace) ++ newFun.getId
    withRef stx do
    let cinfo ← getConstInfo oldFunName
    unless cinfo.hasValue do
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

    let oldEnv ← getEnv

    let mut mvars := []
    let mut mappedValues := #[]
    let mut mappedTypes := #[]

    -- What follows from here is a horrible mess and should definitely be reworked to be more principled in the very near future..
    for {cinfo, newName, isAux, ..} in mapHeaders do
      trace[Modular.Elab] "elaborating {newName}"
      -- If a function isn't an auxiliary, it might be recursive. As such, the shape of the function should be known (i.e we dont' have holes in it for now), and we need the mapping to already exist before translating the term, since the function might itself appear in its `eq_def` body.
      if !isAux then
        -- TODO put behind a function
        let levelParams := cinfo.levelParams
        let newMapEntry := {
          expr := mkConst newName (levelParams.map .param)
          levelParams := levelParams
          numArgs := 0
          numHoles := 0}
        modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry)
        let mappedType ← modMap (← get) cinfo.type
        addDecl <| .axiomDecl
          {  name := newName
             levelParams := cinfo.levelParams
             type := mappedType
             isUnsafe := false }
      let mut mappedValue ← modMapValueOrEqDef cinfo isAux
      if newName.isMatcher then
        trace[Modular.Elab] "matcher detected {newName}"
        mappedValue ← lambdaTelescope mappedValue fun xs e => do
          unless xs.all (! ·.hasMVar) do
            throwError "TODO instantiate vars appropriately to avoid this issue"
          withReplaceMVarsWithFVars e fun e ys => do
            let e ← mkLambdaFVars ys e
            mkLambdaFVars xs e
      else
        let newMvars ← getMVarsNoDelayed mappedValue
        mvars := newMvars.toList ++ mvars
      mappedValues := mappedValues.push mappedValue
      let mappedType ← inferType mappedValue
      if mappedType.hasMVar then
        throwError "Type contains mvars, unfortunate. TODO addDecl while avoiding kernel check so this doesn't throw an error. We will discard this environment anyway as soon as the predefs are elabed."
      mappedTypes := mappedTypes.push mappedType
      if isAux then
        addDecl <| .axiomDecl
          { name := newName
            levelParams := cinfo.levelParams
            type := mappedType
            isUnsafe := false }
        addAuxMapping cinfo.name newName

    trace[Modular.Elab] "Mapped values : {mappedValues}"
    if mvars.isEmpty  then
      if tacs.isSome then
        throwError "Unexpected tactic block: the translation generated no obligations"
    else
      let some tac := tacs
        | throwError "Missing `where` block to solve the missing holes"
      solveGoalsWithTactic tac mvars
    trace[Modular.Elab] "Tactics elaborated"
    mappedValues ← mappedValues.mapM instantiateMVars
    mappedValues.forM fun e => Meta.check e
    if mappedValues.any Expr.hasExprMVar then
      throwError "`mod_def` generated unresolved metavariables"
    addDeclarationRangesFromSyntax newFunName newFun
    let tempAxiomNames : NameSet := Id.run do
      let mut names : NameSet := {}
      for {newName, ..} in mapHeaders do
        names := names.insert newName
      return names
    let retainedRoots := collectExprConstants (mappedValues ++ mappedTypes)
    let retainedDeclMap ← collectRetainedDecls oldEnv tempAxiomNames retainedRoots
    let retainedDecls ← topoSortRetainedDecls retainedDeclMap
    trace[Modular.Elab] "Retaining {retainedDecls.size} generated declarations from tactic elaboration"
    trace[Modular.Elab] "Setting old env back"
    setEnv oldEnv
    replayRetainedDecls retainedDecls
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
                      termination := if isAux then .none else termination_hint }
      predefs := predefs.push predef
    trace[Modular.Elab] "Predefs constructed successfully"
    addPreDefinitions (← getLCtx, ← getLocalInstances) predefs
    trace[Modular.Elab] "Predefs elaborated successfully"

  | _ => throwUnsupportedSyntax

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

set_option pp.match true
#print Nat.add.eq_def

run_cmd liftTermElabM do
  logInfo m!"{(← getMatcherInfo? `Nat.add.match_1) |>.get!}"
