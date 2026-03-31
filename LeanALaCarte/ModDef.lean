import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
import Lean.Parser.Tactic
import LeanALaCarte.CollectDelayedAssignementsWithArgs
import LeanALaCarte.AuxMapping
import LeanALaCarte.CollectAuxDefs
import Lean.Elab.MutualDef
open Lean Parser Elab Meta Command

def Lean.ConstantInfo.kind! (cinfo : ConstantInfo) : DefKind := match cinfo with
  | .defnInfo _ => .def
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | _ => unreachable!

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
  let type ← modmap (← get) cinfo.type
  assert! !type.hasMVar
  return { cinfo, newName, isAux, type }

structure MappedDecl extends MappedHeader where
  value : Expr

/- TODO adapt syntax to take into account:
- docstrings
- attributes
- termination hints
- `where` clauses
- (maybe ?) make the current `by` goals be filled in as holes in `where finally` ? (this would be non-trivial in cases where the holes appear in auxiliary defs rather than the "real" one. One solution could be to inline/delta-reduce auxiliary defs that aren't matchers, and translating the core def directly, leaving the job of re-abstracting relevant parts of the code to the usual elaborator for `PreDef`s. The big danger to doing that is obviously performance. `modmap`ed terms need to be `check`ed to instantiate the type of the introduced mvars for now, and doing so on terms containing very large proof terms (e.g `grind` or `omega` proofs) is bound to be expensive. A solution would be to get rid of `Meta.check` in `modmap`, but I'm confident type-checking is still called a fair few times when elaborating PreDefs, so this doesn't solve the issue of abstracting the proofs at the right time.)

Once that is all done, translate that syntax to a `DefView` and elaborate it like any other function, making use of all the niceties the lean elaborator offers :D
Actually, `DefView` contain the value as a syntax, not as an Expr, this is not ideal because it implies needing to first delaborate the translated term before re-elaborating it.. Let's try to translate things directly to `PreDef`s instead, this will be a bit of a PITA...
-/

syntax (name := modular_mod_def)
  declModifiers "mod_def" ident "extends" ident Termination.suffix (ppDedent(ppLine) "where" ppDedent(ppLine) tacticSeqIndentGt)? : modular_command

@[modular_elab modular_mod_def, incremental]
def elabModDef : ModularElab := fun stx =>
  match stx with
  | `(modular_command| $mod:declModifiers mod_def $newFun extends $oldFun $termination_stx $[where $tacs]?) => liftModularM do
    let modifiers ← elabModifiers mod
    let modifiers := {modifiers with computeKind := .noncomputable} -- For now, generated expressions contain `.brecOns` often, which the lean compiler doesn't currently handle.
    let termination_hint ← elabTerminationHints termination_stx
    -- let mut view ←
      -- withExporting (isExporting := modifiers.visibility.isInferredPublic (← getEnv)) do
        -- mkDefView modifiers _
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun
    let newFunName := (← getCurrNamespace) ++ newFun.getId
    withRef stx do
    let cinfo ← getConstInfo oldFunName
    unless cinfo.hasValue do
      throwError "`mod_def` can only extend declarations defined with `def` or `theorem`"

    -- let oldValue ← unfoldAuxDecls cinfo
    -- let mut mappedValue ← modmap (← get) oldValue

    -- let mvars ← getMVarsNoDelayed mappedValue
    -- unless mvars.isEmpty do
    --   let some tac := tacs
    --     | throwError "missing tactics"
    --   solveGoalsWithTactic tac mvars.toList
    -- mappedValue ← instantiateMVars mappedValue
    -- unless !(mappedValue.hasExprMVar) do
    --   throwError "In {newFunName}: `mod_def` generated unresolved metavariables"
    -- let preDef := { ref := stx
    --                 kind := cinfo.kind!
    --                 levelParams := cinfo.levelParams
    --                 modifiers := modifiers
    --                 declName := newFunName
    --                 binders := .missing
    --                 type := ← inferType mappedValue
    --                 value := mappedValue
    --                 termination := termination_hint }

    -- addPreDefinitions (← getLCtx, ← getLocalInstances) _

    let extraMapNames ← auxDefs oldFunName
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut mapHeaders := #[]
    for oldAuxName in extraMapNames do
      let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
      mapHeaders := mapHeaders.push (← mkMappedDecl oldAuxName newAuxName)
    mapHeaders := mapHeaders.push (← mkMappedDecl oldFunName newFunName false)

    let oldEnv ← getEnv

    for {cinfo, newName, type, ..} in mapHeaders do
      addDecl <| .axiomDecl {  name := newName
                               levelParams := cinfo.levelParams
                               type := type
                               isUnsafe := false }
    let mut mvars := []
    let mut mappedValues := #[]
    for {cinfo, newName, isAux, ..} in mapHeaders do
      if isAux then
        addAuxMapping cinfo.name newName
      else
        -- TODO put behind a function
        let levelParams := cinfo.levelParams
        let newMapEntry := {
          translation := mkConst newName (levelParams.map .param)
          levelParams := levelParams
          numArgs := 0
          numHoles := 0}
        modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry)
    for {cinfo, newName, ..} in mapHeaders do
      trace[Modular.Elab] "elaborating {newName}"
      let map ← get
      let mut mappedValue ← modmap map cinfo.value!
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

    unless mvars.isEmpty do
      let some tac := tacs
        | throwError "Missing `where` block to solve the missing holes"
      solveGoalsWithTactic tac mvars
    mappedValues ← mappedValues.mapM instantiateMVars
    mappedValues.forM fun e => Meta.check e
    if mappedValues.any Expr.hasExprMVar then
      throwError "`mod_def` generated unresolved metavariables"
    addDeclarationRangesFromSyntax newFunName newFun
      /-After that we need to:
        - generate the appropriate predefs from those
        - set the original env back
        - addPreDefinitions
      -/
        -- solveGoalsWithTactic tac mvars.toList
        -- mappedValue ← instantiateMVars mappedValue
        -- unless !(mappedValue.hasExprMVar) do
          -- throwError "In {newName}: `mod_def` generated unresolved metavariables"
        -- checkNotAlreadyDeclared newName
        -- addDecl <| .defnDecl {
          -- name := newName
          -- levelParams := cinfo.levelParams
          -- type := ← inferType mappedValue
          -- value := mappedValue
          -- hints := cinfo.hints
          -- safety := if cinfo.isUnsafe then .unsafe else .safe
        -- }
        -- enableRealizationsForConst newName
        -- if isAux then
          -- addAuxMapping cinfo.name newName
        -- else
          -- let levelParams := cinfo.levelParams
          -- TODO add behind a function
          -- let newMapEntry := {
            -- translation := mkConst newName (levelParams.map .param)
            -- levelParams := levelParams
            -- numArgs := 0
            -- numHoles := 0}
          -- modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry)
      -- if tacs.size > nextTacIdx then
        -- throwError "Too many tactic blocks provided"
      -- addDeclarationRangesFromSyntax newFunName newFun
  | _ => throwUnsupportedSyntax


/- This is super great news, it means we can elaborate many preDefs together, even if they don't have the same levelParams, as long as they're not part of the same SCC, which is exactly what I need !!-/
run_cmd liftTermElabM do
  let preDef1 : PreDefinition := { ref := .missing
                                   kind := .def
                                   levelParams := [`u]
                                   modifiers := default
                                   declName := `test
                                   binders := .missing
                                   type := mkSort (.param `u)
                                   value := mkConst `PUnit [.param `u]
                                   termination := { ref := .missing
                                                    terminationBy?? := none
                                                    terminationBy? := none
                                                    partialFixpoint? := none
                                                    decreasingBy? := none
                                                    extraParams := 0 } }
  let preDef2 : PreDefinition := { ref := .missing
                                   kind := .def
                                   levelParams := []
                                   modifiers := default
                                   declName := `test2
                                   binders := .missing
                                   type := mkSort 0
                                   value := mkConst `test [0]
                                   termination := { ref := .missing
                                                    terminationBy?? := none
                                                    terminationBy? := none
                                                    partialFixpoint? := none
                                                    decreasingBy? := none
                                                    extraParams := 0 } }
  addPreDefinitions (← getLCtx, ← getLocalInstances) #[preDef1,preDef2]
