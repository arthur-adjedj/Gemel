import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
import Lean.Parser.Tactic
import LeanALaCarte.CollectDelayedAssignementsWithArgs
import LeanALaCarte.AuxMapping
open Lean Parser Elab Meta Command

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

syntax (name := modular_mod_def)
  "mod_def" ident "extends" ident "by" ppLine tacticSeq : modular_command

def withReplaceMVarsWithFVars [Inhabited α] (e: Expr) (k : Expr → Array Expr → MetaM α) : MetaM α := do
  let delayedMvarsWithArgs ← e.collectDelayedAssignmentsWithArgs
  let mvarsWithAppTy ← delayedMvarsWithArgs.mapM fun e => do
    let mvar := e.getAppFn.mvarId!
    let mvarTy ← mvar.getType'
    let args := e.getAppArgs
    forallBoundedTelescope mvarTy args.size fun xs ty => return ty.replaceFVars xs args
  trace[Modular.Elab] "delayedMvarsWithArgs : {delayedMvarsWithArgs}"
  trace[Modular.Elab] "mvarsWithAppTy : {mvarsWithAppTy}"
  let decls ← mvarsWithAppTy.mapM fun ty => do return (← mkFreshId,ty)
  withLocalDeclsDND decls fun xs =>
  let e := e.replace fun t =>
    -- TODO ptreq should work here, if it doesn't, use normal equality
    delayedMvarsWithArgs.findIdx? (unsafe ptrEq t ·) |>.map fun idx => xs[idx]!
  k e xs

@[modular_elab modular_mod_def, incremental]
def elabModDef : ModularElab := fun stx => do
  match stx with
  | `(modular_command| mod_def $newFun:ident extends $oldFun:ident by $tac:tacticSeq) => do
    let oldFunName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo oldFun
    let oldFunName := oldFunName.eraseMacroScopes
    let newFunName := (← getCurrNamespace) ++ newFun.getId
    let map ← get
    withRef stx do
    let levelParams ← do
      let info ← getConstInfo oldFunName
      pure info.levelParams
    let cinfo ← getConstInfo oldFunName
    unless cinfo.hasValue do
      throwError "`mod_def` can only extend declarations defined with `def` or `theorem`"

    let extraMapNames ← do
      let constants :=
        cinfo.type.foldConsts (init := ({} :  Std.HashSet Name)) fun constName cs =>
          cs.insert constName.eraseMacroScopes
      let constants := cinfo.value!.foldConsts (init := constants) fun constName cs =>
          cs.insert constName.eraseMacroScopes

      let mut aux_defs := []

      for constName in constants do
        if map[constName]?.isNone then
          if oldFunName.isPrefixOf constName then
            aux_defs := constName::aux_defs
          -- let cinfo ← getConstInfo constName
          -- let constType := cinfo.type
          -- let mappedConstType ← modmap map constType
          -- unless (← isDefEq constType mappedConstType) do
            -- throwError m!"Cannot modularly translate declaration: constant `{constName}` has no partial mapping, and its translated type is not definitionally equal to its original type\noriginal:{indentExpr constType}\ntranslated:{indentExpr mappedConstType}"
      pure aux_defs
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let extraMapEntries ← liftTermElabM do
      let mut extraMapEntries := []
      for oldAuxName in extraMapNames do
        let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
        checkNotAlreadyDeclared newAuxName
        let oldAuxInfo ← getConstInfo oldAuxName
        unless oldAuxInfo.hasValue do
          throwError "Failed to translate auxiliary declaration {oldAuxName}, expected `def` or `theorem`"
        let mappedAuxValue ← modmap map oldAuxInfo.value!
        let mappedAuxValue ← lambdaTelescope mappedAuxValue fun xs e => do
          unless xs.all (! ·.hasMVar) do
            throwError "TODO instantiate vars appropriately to avoid this issue"
          withReplaceMVarsWithFVars e fun e ys => do
            let e ← mkLambdaFVars ys e
            mkLambdaFVars xs e
        let mappedAuxType ← inferType mappedAuxValue
        checkNotAlreadyDeclared newAuxName
        addDecl <| .defnDecl {
          name := newAuxName
          levelParams := oldAuxInfo.levelParams
          type := mappedAuxType
          value := mappedAuxValue
          hints := oldAuxInfo.hints
          safety := if oldAuxInfo.isUnsafe then .unsafe else .safe
        }
        enableRealizationsForConst newAuxName
        if (← getEnv).contains newAuxName then
          extraMapEntries := (← mkAuxMapping oldAuxName newAuxName) :: extraMapEntries
      return extraMapEntries
    modify fun m => m.insertMany extraMapEntries
    -- let mappedType ← modmap map unfoldedType
    -- let tyMVars := mappedType.collectMVars {}
    let map ← get
    liftTermElabM do
      let mappedValue ←  modmap map cinfo.value!
      let tacticMvars ← getMVarsNoDelayed mappedValue
      trace[Modular.Elab] "mvars collected: {tacticMvars.map Expr.mvar}"
      solveGoalsWithTactic tac tacticMvars.toList

      -- let mappedType ← instantiateMVars mappedType
      let mappedValue ← instantiateMVars mappedValue
      unless !(mappedValue.hasExprMVar) do
        throwError "`mod_def` generated unresolved metavariables"

      checkNotAlreadyDeclared newFunName
      addDecl <| .defnDecl {
        name := newFunName
        levelParams := cinfo.levelParams
        type := ← inferType mappedValue
        value := mappedValue
        hints := cinfo.hints
        safety := if cinfo.isUnsafe then .unsafe else .safe
      }
      enableRealizationsForConst newFunName
    addDeclarationRangesFromSyntax newFunName newFun

    let newMapEntry : ModularExtension := {
      translation := mkConst newFunName (levelParams.map .param)
      levelParams := levelParams
      numArgs := 0
      numHoles := 0
    }
    modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry) --.insertMany extraMapEntries
  | _ => throwUnsupportedSyntax
