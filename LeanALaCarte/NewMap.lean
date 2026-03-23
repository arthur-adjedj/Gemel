import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
import Lean.Parser.Tactic
import LeanALaCarte.CollectDelayedAssignementsWithArgs

open Lean Parser Elab Meta Command

private def getArrowBinderNames (type : Expr) : Array Name :=
  let rec go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b => go b acc
    | _ => acc
  go type #[]

private def mkAuxMapping (oldName newName : Name) : TermElabM (Name × ModularExtension) := do
  let oldInfo ← getConstInfo oldName
  let newInfo ← getConstInfo newName
  let oldNumArgs := (getArrowBinderNames oldInfo.type).size
  let newNumArgs := (getArrowBinderNames newInfo.type).size
  unless oldNumArgs <= newNumArgs do
    throwError m!"Unexpected auxiliary mapping arity from `{oldName}` to `{newName}`\nThe new declaration has fewer arguments ({newNumArgs}) than the old one ({oldNumArgs})"
  let numExtraArgs := newNumArgs - oldNumArgs
  let oldArgBVar (i : Nat) : Expr := mkBVar (oldNumArgs - 1 - i)
  let holeBVar (i : Nat) : Expr := mkBVar (oldNumArgs + (numExtraArgs - 1 - i))
  let mut auxArgs : Array Expr := #[]
  for i in [:oldNumArgs] do
    auxArgs := auxArgs.push (oldArgBVar i)
  for i in [:numExtraArgs] do
    auxArgs := auxArgs.push (holeBVar i)
  let translation := mkAppN (mkConst newName (oldInfo.levelParams.map .param)) auxArgs
  let auxExt : ModularExtension := {
    translation
    levelParams := oldInfo.levelParams
    numArgs := oldNumArgs
    numHoles := numExtraArgs
  }
  return (oldName.eraseMacroScopes, auxExt)

syntax "map_fn" ident+ "⇒" term : modular_command

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
    let defnVal ←
      match cinfo with
      | .defnInfo defnVal => pure defnVal
      | _ => throwError "`mod_def` can only extend declarations defined with `def`"

    let extraMapNames ← do
      let constants :=
        defnVal.type.foldConsts (init := ({} :  Std.HashSet Name)) fun constName cs =>
          cs.insert constName.eraseMacroScopes
      let constants := defnVal.value.foldConsts (init := constants) fun constName cs =>
          cs.insert constName.eraseMacroScopes

      let mut aux_defs := []

      for constName in constants do
        if map[constName]?.isNone then
          if constName.isInternalDetail then
            aux_defs := constName::aux_defs
          -- let cinfo ← getConstInfo constName
          -- let constType := cinfo.type
          -- let mappedConstType ← modmap map constType
          -- unless (← isDefEq constType mappedConstType) do
            -- throwError m!"Cannot modularly translate declaration: constant `{constName}` has no partial mapping, and its translated type is not definitionally equal to its original type\noriginal:{indentExpr constType}\ntranslated:{indentExpr mappedConstType}"
      pure aux_defs
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let extraMapEntries ← liftTermElabM do
      let env ← getEnv
      let mut extraMapEntries := []
      for oldAuxName in extraMapNames do
        let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
        if env.contains newAuxName then
          throwError "uh"
        let oldAuxInfo ← getConstInfoDefn oldAuxName
        let mappedAuxValue ← modmap map oldAuxInfo.value
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
          safety := oldAuxInfo.safety
        }
        if (← getEnv).contains newAuxName then
          extraMapEntries := (← mkAuxMapping oldAuxName newAuxName) :: extraMapEntries
      return extraMapEntries
    modify fun m => m.insertMany extraMapEntries
    -- let mappedType ← modmap map unfoldedType
    -- let tyMVars := mappedType.collectMVars {}
    let map ← get
    liftTermElabM do
      let mappedValue ←  modmap map defnVal.value
      let mvars := mappedValue.collectMVars {} --tyMVars
      -- TODO rather than recollect the right mvars, we might as well collect them through `modmap`
      trace[Modular.Elab] "mvars collected: {mvars.result.map Expr.mvar}"
      let tacticMvars ←  mvars.result.mapM getDelayedMVarRoot
      trace[Modular.Elab] "mvar roots: {tacticMvars.map Expr.mvar}"
      solveGoalsWithTactic tac tacticMvars.toList

      -- let mappedType ← instantiateMVars mappedType
      let mappedValue ← instantiateMVars mappedValue
      unless !(mappedValue.hasExprMVar) do
        throwError "`mod_def` generated unresolved metavariables"

      checkNotAlreadyDeclared newFunName
      addDecl <| .defnDecl {
        name := newFunName
        levelParams := defnVal.levelParams
        type := ← inferType mappedValue
        value := mappedValue
        hints := defnVal.hints
        safety := defnVal.safety
      }
    addDeclarationRangesFromSyntax newFunName newFun

    let newMapEntry : ModularExtension := {
      translation := mkConst newFunName (levelParams.map .param)
      levelParams := levelParams
      numArgs := 0
      numHoles := 0
    }
    modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry) --.insertMany extraMapEntries
  | _ => throwUnsupportedSyntax
