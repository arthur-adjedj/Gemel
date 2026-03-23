import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
import Lean.Meta.Constructions
open Lean Parser Elab Meta Command


/-- Bundle of the various syntax elements of an extended inductive, to be elaborated as an `ExtendedInd` later -/
structure ExtendedIndView where
  -- TODO
  -- notes: Don't forget to include things like attributes, check what's in `InductiveView` and what should/shouldn't be kept/used here.
  -- One current limitation is that Lean does not record what attributes where applied to a given declaration, so copying/adapting the

/- TODO extend structure to manage mutual types -/
structure ExtendedInd where
  newIndName : Name
  numParams : Nat
  levelParams : List Name
  type : Expr
  /-We ideally want extensions to extend arbitrary inductives family instantiations , not just the base case, e.g consider cases like:`inductive Foo (A) extends Prod A A where ...`.
  (Instantiating type parameters of the extended types here makes sense to me, instantiating indices not so much.)
  In practice, the toy system currently implemented simply maps from constant names to Exprs, so it wouldn't work for such cases. Instead, the real implementation will have to rely on something to unify patterns, e.g using `DiscrTree`s-/
  indNames : Array Name
  addedConstrs : Array Constructor


def ExtendedInd.toInductiveView (map : ModularMap) (e : ExtendedInd) : MetaM InductiveType := do
  let indVals ← e.indNames.mapM getConstInfoInduct
  let inheritedCtors ← indVals.foldlM (init := []) fun acc indVal => do
    return (← indVal.ctors.mapM getConstInfoCtor) ++ acc
  withLocalDeclD e.newIndName e.type fun newIndFVar => do
    let tempIndExt : ModularExtension := {
      translation := newIndFVar
      levelParams := []
      numArgs := 0
      numHoles := 0
    }
    let tempMap := e.indNames.foldl (init := map) fun acc indName =>
      acc.insert indName.eraseMacroScopes tempIndExt
    let tempMap := tempMap.insert e.newIndName.eraseMacroScopes tempIndExt
    let newIndConst := mkConst e.newIndName (e.levelParams.map .param)
    let inheritedCtors ← inheritedCtors.mapM fun ctor => do
      let ctorType ← modmap tempMap ctor.type
      unless !ctorType.hasMVar do
        -- TODO this inductive translation is partial and requires the user to complete holes, this is not implemented yet.
        throwError "Failed to translate constructor {ctor.name}: the translation generated holes. TODO expose a way to fill these holes."
      let ctorType := ctorType.replace fun
        | .fvar fvarId =>
          if fvarId == newIndFVar.fvarId! then some newIndConst else none
        | _ => none
      return ({
        name := ctor.name.replacePrefix ctor.induct e.newIndName
        type := ctorType
      } : Constructor)
    let addedCtors := e.addedConstrs
    return {
      name := e.newIndName
      type := e.type
      ctors := inheritedCtors ++ addedCtors.toList
    }

/- TODO
  - Make syntax for inductive extension
  - Add translation of ind type, ind constrs and ind recursors to the modular map
  - Experiment with adding translation for auxiliary defs too
-/
private def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams

private def getArrowBinderNames (type : Expr) : Array Name :=
  let rec go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b => go b acc
    | _ => acc
  go type #[]

private def replaceArrowBinderNames (type : Expr) (newNames : Array Name) : Expr :=
  let rec go (type : Expr) (i : Nat) : Expr :=
    if h : i < newNames.size then
      match type with
      | .forallE n d b bi =>
        if n.hasMacroScopes then
          mkForall newNames[i] bi d (go b (i + 1))
        else
          mkForall n bi d (go b (i + 1))
      | _ => type
    else
      type
  go type 0

private def reorderCtorArgs (ctorType : Expr) : MetaM Expr := do
  forallTelescopeReducing ctorType fun as type => do
    let bs := type.getAppArgs
    let mut as := as
    let mut bsPrefix := #[]
    for b in bs do
      unless b.isFVar && as.contains b do
        break
      let localDecl ← getFVarLocalDecl b
      if localDecl.binderInfo.isExplicit then
        break
      unless localDecl.userName.hasMacroScopes do
        break
      unless !(← localDeclDependsOnPred localDecl fun fvarId => as.any fun p => p.fvarId! == fvarId) do
        break
      bsPrefix := bsPrefix.push b
      as := as.erase b
    if bsPrefix.isEmpty then
      return ctorType
    else
      let r ← mkForallFVars (bsPrefix ++ as) type
      let C := type.getAppFn
      let binderNames := getArrowBinderNames (← instantiateMVars (← inferType C))
      return replaceArrowBinderNames r binderNames[*...bsPrefix.size]

private partial def checkParamOccs (indFVars : Array Expr) (params : Array Expr) (ctorType : Expr) : MetaM Expr := do
  let rec visit (e : Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      if indFVars.contains f then
        let args := e.getAppArgs
        unless args.size >= params.size do
          throwError m!"Invalid recursive occurrence{indentExpr e}\nExpected at least {params.size} parameter argument(s), got {args.size}"
        for i in [:params.size] do
          let param := params[i]!
          let arg := args[i]!
          unless (← isDefEq param arg) do
            throwError m!"Mismatched inductive type parameter in{indentExpr e}\nThe provided argument{indentExpr arg}\nis not definitionally equal to the expected parameter{indentExpr param}"
        args.forM visit
      else
        visit e.appFn! *> visit e.appArg!
    | .forallE _ d b _ => visit d *> visit b
    | .lam _ d b _ => visit d *> visit b
    | .letE _ t v b _ => visit t *> visit v *> visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => pure ()
  visit ctorType
  return ctorType

private def elabExtendedCtors (newIndName : Name) (newLevelParams : List Name) (indType : Expr) (numParams : Nat)
  (ctors : Array Syntax) : TermElabM (Array Constructor) := do
  withLocalDeclD newIndName indType fun indFVar => do
    let newIndConst := mkConst newIndName (newLevelParams.map .param)
    forallTelescopeReducing indType fun allArgs _ => do
      let params := allArgs.extract 0 numParams
      let indices := allArgs.extract numParams allArgs.size
      withExplicitToImplicit params do
        let indFamily ← isInductiveFamily params.size indFVar
        ctors.mapM fun ctorStx => withRef ctorStx do
          let (binders, type?) := expandOptDeclSig ctorStx[4]
          let ctorName := ctorStx.getIdAt 3
          Term.withAutoBoundImplicit <|
            Term.elabBinders binders.getArgs fun ctorParams => withRef ctorStx do
              let elabCtorType : TermElabM Expr := do
                match type? with
                | none =>
                  if indFamily then
                    throwError "Missing resulting type for constructor `{ctorName}`: Its resulting type must be specified because it is part of an inductive family declaration"
                  return mkAppN indFVar params
                | some ctorTypeStx =>
                  let type ← Term.elabType ctorTypeStx
                  Term.synthesizeSyntheticMVars (postpone := .yes)
                  let type ← instantiateMVars type
                  let type ← checkParamOccs #[indFVar] params type
                  forallTelescopeReducing type fun _ resultingType => do
                    unless resultingType.getAppFn == indFVar do
                      throwError m!"Unexpected resulting type{indentExpr resultingType}\nExpected an application of `{newIndName}`"
                    unless (← isType resultingType) do
                      throwError m!"Unexpected resulting term{indentExpr resultingType}\nThe constructor `{ctorName}` must return a type"
                  return type
              let type ← elabCtorType
              Term.synthesizeSyntheticMVarsNoPostponing
              let ctorParams ← Term.addAutoBoundImplicits ctorParams (ctorStx[3].getTailPos? (canonicalOnly := true))
              let except (mvarId : MVarId) := ctorParams.any fun ctorParam => ctorParam.isMVar && ctorParam.mvarId! == mvarId
              let extraCtorParams ← Term.collectUnassignedMVars (← instantiateMVars type) #[] except
              let type ← mkForallFVars (extraCtorParams ++ ctorParams) type
              let type ← reorderCtorArgs type
              let type ← mkForallFVars indices type
              let type ← mkForallFVars params type
              let type := type.replace fun
                | .fvar fvarId =>
                  if fvarId == indFVar.fvarId! then some newIndConst else none
                | _ => none
              return {
                name := newIndName ++ ctorName
                type := type
              }

syntax (name := modular_inductive) "inductive" ident (ppSpace bracketedBinder)* "extends" term,+ "where" ctor* :  modular_command
def elabExtendedInd (stx : Syntax) : TermElabM ExtendedInd := do
  match stx with
  | `(modular_command|inductive $i $[$params]* extends $inds,* where $ctors*) => do
    let newIndName := i.getId --TODO this is wrong..? namespace handling is hard..
    Term.withAutoBoundImplicit <|
      Term.elabBinders params fun declaredParams => do
        let indExprs ← inds.getElems.mapM fun indStx => do
          let indExpr ← Term.elabTerm indStx none
          instantiateMVars indExpr
        let mut indNames : Array Name := #[]
        for indExpr in indExprs do
          match indExpr.getAppFn with
          | .const indName _ =>
            indNames := indNames.push indName.eraseMacroScopes
          | _ =>
            throwError m!"Expected an application of an inductive constant in `extends`, got{indentExpr indExpr}"
        let indVals ← indNames.mapM getConstInfoInduct
        let {levelParams, type, numParams := baseNumParams,  ..} := indVals[0]!
        unless ← indVals[1:].allM (fun indVal => pure (indVal.levelParams == levelParams) <&&> isDefEq indVal.type type) do
          throwError "invalid types between inductives being extended"
        unless declaredParams.size <= baseNumParams do
          throwError m!"Expected at most {baseNumParams} parameter binder(s), got {declaredParams.size}"
        if declaredParams.size > 0 then
          let firstArgs := indExprs[0]!.getAppArgs
          unless firstArgs.size >= declaredParams.size do
            throwError m!"Expected at least {declaredParams.size} parameter argument(s) in `extends` target"
          for i in [:declaredParams.size] do
            unless (← isDefEq firstArgs[i]! declaredParams[i]!) do
              throwError m!"Parameter binder mismatch in `extends` target at position {i+1}"
        let defaultNumParams := if declaredParams.size == 0 then baseNumParams else declaredParams.size
        let (numParams, addedConstrs) ←
          if declaredParams.size == 0 && baseNumParams > 0 then
            try
              pure (defaultNumParams, (← elabExtendedCtors newIndName levelParams type defaultNumParams ctors))
            catch _ =>
              pure (0, (← elabExtendedCtors newIndName levelParams type 0 ctors))
          else
            pure (defaultNumParams, (← elabExtendedCtors newIndName levelParams type defaultNumParams ctors))
        return { newIndName, numParams, levelParams, type, indNames, addedConstrs }
  | _ => throwUnsupportedSyntax

def addInductiveMappings (extendedInductive : ExtendedInd) : ModularElabM Unit := do
  let mut maps : List (Name × ModularExtension):= []
  let newIndName := extendedInductive.newIndName
  let newIndParams := extendedInductive.levelParams
  let newIndLevels := newIndParams.map .param
  let newRecName := mkRecName newIndName
  let numAddedCtors := extendedInductive.addedConstrs.size
  let indExt : ModularExtension := { translation := mkConst newIndName newIndLevels
                                     levelParams := newIndParams
                                     numArgs := 0
                                     numHoles := 0 }
  let mkAuxMapping (oldName newName : Name) : ModularElabM (Name × ModularExtension) := do
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
    let auxExt : ModularExtension := {
      translation := mkAppN (mkConst newName (oldInfo.levelParams.map .param)) auxArgs
      levelParams := oldInfo.levelParams
      numArgs := oldNumArgs
      numHoles := numExtraArgs
    }
    return (oldName.eraseMacroScopes, auxExt)
  for indName in extendedInductive.indNames do
    maps := (indName.eraseMacroScopes,indExt)::maps
    let indVal ← getConstInfoInduct indName
    for ctor in indVal.ctors do
      let newCtorName := ctor.replacePrefix indName newIndName
      let ctorExt : ModularExtension := { translation := mkConst newCtorName newIndLevels
                                          levelParams := newIndParams
                                          numArgs := 0
                                          numHoles := 0 }
      maps := (ctor.eraseMacroScopes,ctorExt)::maps
    let oldRecName := mkRecName indName
    if let .recInfo oldRecVal ← getConstInfo oldRecName then
      let env ← getEnv
      let oldNumArgs := (getArrowBinderNames oldRecVal.type).size
      let oldPrefix := oldRecVal.numParams + oldRecVal.numMotives
      let tailStart := oldPrefix + oldRecVal.numMinors
      let numExtraMinors := numAddedCtors * oldRecVal.numMotives
      let oldArgBVar (i : Nat) : Expr := mkBVar (oldNumArgs - 1 - i)
      let holeBVar (i : Nat) : Expr := mkBVar (oldNumArgs + (numExtraMinors - 1 - i))
      let mut recArgs : Array Expr := #[]
      for i in [:tailStart] do
        recArgs := recArgs.push (oldArgBVar i)
      for i in [:numExtraMinors] do
        recArgs := recArgs.push (holeBVar i)
      for i in [tailStart:oldNumArgs] do
        recArgs := recArgs.push (oldArgBVar i)
      let recExt : ModularExtension := {
        translation := mkAppN (mkConst newRecName (oldRecVal.levelParams.map .param)) recArgs
        levelParams := oldRecVal.levelParams
        numArgs := oldNumArgs
        numHoles := numExtraMinors
      }
      maps := (oldRecName.eraseMacroScopes, recExt) :: maps
      let oldRecOnName := mkRecOnName indName
      let newRecOnName := mkRecOnName newIndName
      if env.contains oldRecOnName && env.contains newRecOnName then
        maps := (← mkAuxMapping oldRecOnName newRecOnName) :: maps
      let oldCasesOnName := mkCasesOnName indName
      let newCasesOnName := mkCasesOnName newIndName
      if env.contains oldCasesOnName && env.contains newCasesOnName then
        maps := (← mkAuxMapping oldCasesOnName newCasesOnName) :: maps
      let oldBelowName := mkBelowName indName
      let newBelowName := mkBelowName newIndName
      if env.contains oldBelowName && env.contains newBelowName then
        maps := (← mkAuxMapping oldBelowName newBelowName) :: maps
      let oldBRecOnName := mkBRecOnName indName
      let newBRecOnName := mkBRecOnName newIndName
      if env.contains oldBRecOnName && env.contains newBRecOnName then
        maps := (← mkAuxMapping oldBRecOnName newBRecOnName) :: maps
  modify fun map => map.insertMany maps

@[modular_elab modular_inductive, incremental]
def elabExtendedInductive : ModularElab := fun stx => do
  let extendedInd ← liftTermElabM <| elabExtendedInd stx
  let map ← get
  trace[Modular.Elab] m!"modmap : {(← get).toList}"
  liftTermElabM do
    let extendedInductive ← extendedInd.toInductiveView map
    trace[Modular.Elab] m!"extendedInductive ctors : {extendedInductive.ctors.map Constructor.type}"
    addDecl (.inductDecl extendedInd.levelParams extendedInd.numParams [extendedInductive] false)
    mkRecOn extendedInd.newIndName
    let env ← getEnv
    let hasUnit := env.contains ``PUnit
    let hasProd := env.contains ``Prod
    if hasUnit then
      mkCasesOn extendedInd.newIndName
    if hasUnit && hasProd then
      mkBelow extendedInd.newIndName
      mkBRecOn extendedInd.newIndName
  addInductiveMappings extendedInd
  -- TODO? add mappings for `SizeOf` and related ?
