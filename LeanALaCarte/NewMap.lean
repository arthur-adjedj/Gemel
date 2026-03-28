import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
import Lean.Parser.Tactic
import LeanALaCarte.CollectDelayedAssignementsWithArgs
import LeanALaCarte.AuxMapping
import LeanALaCarte.CollectAuxDefs
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

def Lean.Name.isMatcher : Name → Bool
  | .str _ s   => matchPrefix s "match_"
  | _ => false
where
  /-- Check that a string begins with the given prefix, and then is only digits/'_'. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all fun c => c.isDigit || c == '_')

structure MappedDecl where
  cinfo : ConstantInfo
  newName : Name
  isAux : Bool

def mkMappedDecl (oldName newName : Name) (isAux : Bool := true): MetaM MappedDecl := do
  let cinfo ← getConstInfo oldName
  return { cinfo
           newName
           isAux}


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
  "mod_def" ident "extends" ident (colGe "by" ppLine tacticSeq)* : modular_command

syntax (name := modular_better_mod_def)
  declModifiers "new_mod_def" ident "extends" ident Termination.suffix (Term.whereDecls)? : modular_command

@[modular_elab modular_mod_def, incremental]
def elabModDef : ModularElab := fun stx => liftModularM do
  match stx with
  | `(modular_command| mod_def $newFun:ident extends $oldFun:ident $[by $tacs:tacticSeq]*) => do
    let oldFunName ← realizeGlobalConstNoOverloadWithInfo oldFun
    let oldFunName := oldFunName.eraseMacroScopes
    let newFunName := (← getCurrNamespace) ++ newFun.getId
    withRef stx do
    let cinfo ← getConstInfo oldFunName
    let levelParams := cinfo.levelParams
    unless cinfo.hasValue do
      throwError "`mod_def` can only extend declarations defined with `def` or `theorem`"

    let extraMapNames ← auxDefs oldFunName
    trace[Modular.Elab] m!"auxiliary definitions to be translated: {extraMapNames}"
    let mut toMapDecls := #[]
    for oldAuxName in extraMapNames do
      let newAuxName := oldAuxName.replacePrefix oldFunName newFunName
      toMapDecls := toMapDecls.push (← mkMappedDecl oldAuxName newAuxName)
    toMapDecls := toMapDecls.push (← mkMappedDecl oldFunName newFunName false)

    let mut nextTacIdx : Nat := 0
    for {cinfo, newName, isAux} in toMapDecls do
      trace[Modular.Elab] "elaborating {newName} (nextTacIdx := {nextTacIdx})"
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
        if mappedValue.hasMVar then
          let some tac := tacs[nextTacIdx]?
            | throwError "missing tactics"
          let mvars ← getMVarsNoDelayed mappedValue
          solveGoalsWithTactic tac.raw mvars.toList
          mappedValue ← instantiateMVars mappedValue
          nextTacIdx := nextTacIdx + 1
          unless !(mappedValue.hasExprMVar) do
            throwError "In {newName}: `mod_def` generated unresolved metavariables"
      checkNotAlreadyDeclared newName
      addDecl <| .defnDecl {
        name := newName
        levelParams := cinfo.levelParams
        type := ← inferType mappedValue
        value := mappedValue
        hints := cinfo.hints
        safety := if cinfo.isUnsafe then .unsafe else .safe
      }
      enableRealizationsForConst newName
      if isAux then
        addAuxMapping cinfo.name newName
      else
        -- TODO add behind a function
        let newMapEntry := {
          translation := mkConst newName (levelParams.map .param)
          levelParams := levelParams
          numArgs := 0
          numHoles := 0}
        modify fun m => (m.insert oldFunName.eraseMacroScopes newMapEntry)
    if tacs.size > nextTacIdx then
      throwError "Too many tactic blocks provided"
    addDeclarationRangesFromSyntax newFunName newFun
  | _ => throwUnsupportedSyntax
