module

public meta import Lean.Meta.Constructions.CtorIdx
public meta import Lean.Meta.Constructions.CtorElim
public meta import Lean.Elab.MutualInductive
public meta import Lean.Meta.IndPredBelow
public meta import Lean.Meta.Injective
public import LeanALaCarte.AuxMapping
public import LeanALaCarte.ModMap

public meta section

open Lean Parser Elab Meta Command

namespace IndExtension

/-- Encodes the extension of some inductive by some other inductive types. We constrain such extensions such that they are only allowed on types with the same number of universes, and same parameters/indices. Adding/Removing parameters/indices should be done as part of a separate inductive extension ran before the addition of new constructors. -/
structure AddInd where
  /-We ideally want extensions to extend arbitrary inductives family instantiations , not just the base case, e.g consider cases like:`inductive Foo (A) extends Prod A A where ...`.
  (Instantiating type parameters of the extended types here makes sense to me, instantiating indices not so much.)
  In practice, the toy system currently implemented simply maps from constant names to Exprs, so it wouldn't work for such cases. Instead, the real implementation will have to rely on something to unify patterns, e.g using `DiscrTree`s-/
  indName : Name

/-- Encodes the extension of some inductive types by adding new constructors. We constrain such extensions such that they are only allowed on types with the same number of universes, and same parameters/indices. Adding/Removing parameters/indices should be done as part of a separate inductive extension ran before the addition of new constructors.  -/
structure AddCtors where
  lparams : List Name
  indType : Expr
  addedCtors : Array Constructor

inductive _root_.IndExtension where
  | addCtors : AddCtors → IndExtension
  | addInd : AddInd → IndExtension

end IndExtension

/- TODO extend structure to manage mutual types -/
structure ExtendedInd where
  newIndName : Name
  numParams : Nat
  levelParams : List Name
  origType : Expr
  type : Expr
  extension : IndExtension

def IndExtension.AddInd.modifyInductiveView (e : ExtendedInd) (indFVar : Expr) (tempIndExt : ModularExtension) (oldCtors : List Constructor)(addInd : AddInd): ModularM InductiveType := do
  let indVal ← getConstInfoInduct addInd.indName
  let inheritedCtors ← indVal.ctors.mapM getConstInfoCtor
  let tempMap := (← getMap).insert addInd.indName.eraseMacroScopes tempIndExt
  let tempMap := tempMap.insert e.newIndName.eraseMacroScopes tempIndExt
  withSetMap tempMap do
  let newIndConst := mkConst e.newIndName (e.levelParams.map .param)
  let inheritedCtors ← inheritedCtors.mapM fun ctor => do
    let ctorType ← modMap ctor.type
    unless !ctorType.hasMVar do
      -- TODO this inductive translation is partial and requires the user to complete holes, this is not implemented yet.
      throwError "Failed to translate constructor {ctor.name}: the translation generated holes. TODO expose a way to fill these holes."
    let ctorType := ctorType.replace fun
      | .fvar fvarId =>
        if fvarId == indFVar.fvarId! then some newIndConst else none
      | _ => none
    return {
      name := ctor.name.replacePrefix ctor.induct e.newIndName
      type := ctorType : Constructor
    }
  return { name := e.newIndName
           type := e.type
           ctors := oldCtors ++ inheritedCtors}

def IndExtension.AddCtors.modifyInductiveView (e : ExtendedInd) (oldCtors : List Constructor) (addCtors : AddCtors): ModularM InductiveType :=
  return { name := e.newIndName
           type := e.type
           ctors := oldCtors ++ addCtors.addedCtors.toList}

def IndExtension.modifyInductiveView (e : ExtendedInd) (indFVar : Expr) (tempIndExt : ModularExtension) (oldCtors : List Constructor) : IndExtension → ModularM InductiveType
  | .addCtors a => a.modifyInductiveView e oldCtors
  | .addInd a => a.modifyInductiveView e indFVar tempIndExt oldCtors

def ExtendedInd.toInductiveView (oldCtors : List Constructor) (e : ExtendedInd) : ModularM InductiveType := do
  withLocalDeclD e.newIndName e.origType fun newIndFVar => do
    let .cdecl i fvarId u _ bi k := (← getLCtx).get! newIndFVar.fvarId! | unreachable!
    let mappedDecl := .cdecl i fvarId u e.type bi k
    withReader (fun lctx => lctx.addDecl mappedDecl) do
      let tempIndExt : ModularExtension := {
        expr := newIndFVar
        levelParams := []
        numArgs := 0
        numHoles := 0
      }
      e.extension.modifyInductiveView e newIndFVar tempIndExt oldCtors

def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams

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

partial def checkParamOccs (indFVars : Array Expr) (params : Array Expr) (ctorType : Expr) : MetaM Expr := do
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

def elabCtorType (type? : Option Syntax) (indFVar : Expr) (ctorName : Name) (params : Array Expr): TermElabM Expr := do
  match type? with
  | none => do
    let indFamily ← isInductiveFamily params.size indFVar
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
        throwError m!"Unexpected resulting type{indentExpr resultingType}\nExpected an application of `{indFVar}`"
      unless (← isType resultingType) do
        throwError m!"Unexpected resulting term{indentExpr resultingType}\nThe constructor `{ctorName}` must return a type"
    return type

def elabExtendedCtors (newShortIndName newIndName : Name) (newLevelParams : List Name) (indType : Expr) (numParams : Nat)
  (ctors : Array Syntax) : TermElabM (Array Constructor) :=
  withAuxDecl newIndName indType newShortIndName fun indFVar => do
    let newIndConst := mkConst newIndName (newLevelParams.map .param)
    forallBoundedTelescope indType numParams fun params _ => withExplicitToImplicit params do
    ctors.mapM fun ctorStx => withRef ctorStx do
      let (binders, type?) := expandOptDeclSig ctorStx[4]
      let ctorName := ctorStx.getIdAt 3
      Term.withAutoBoundImplicit <|
        Term.elabBinders binders.getArgs fun ctorParams => do
          let type ← elabCtorType type? indFVar ctorName params
          Term.synthesizeSyntheticMVarsNoPostponing
          let ctorParams ← Term.addAutoBoundImplicits ctorParams (ctorStx[3].getTailPos? (canonicalOnly := true))
          let except (mvarId : MVarId) := ctorParams.any fun ctorParam => ctorParam.isMVar && ctorParam.mvarId! == mvarId
          let extraCtorParams ← Term.collectUnassignedMVars (← instantiateMVars type) #[] except
          let type ← mkForallFVars (extraCtorParams ++ ctorParams) type
          let type ← mkForallFVars params type
          let type := type.replaceFVar indFVar newIndConst
          return {
            name := newIndName ++ ctorName
            type := type
          }

syntax (name := modular_inductive) "inductive" ident (ppSpace bracketedBinder)* "extends" term,+ "where" ctor* :  modular_command
def elabExtendedInd (map : ModularMap) (stx : Syntax) : TermElabM (List ExtendedInd) := do
  match stx with
  | `(modular_command|inductive $i $[$params]* extends $inds,* where $ctors*) => do
    Term.withAutoBoundImplicit do
    Term.elabBinders params fun declaredParams => do
    let indExprs ← inds.getElems.mapM fun indStx => do
      let indExpr ← Term.elabTerm indStx none
      instantiateMVars indExpr
    let mut indNames : Array Name := #[]
    for indExpr in indExprs do
      let .const indName _ := indExpr.getAppFn
        | throwError m!"Expected an application of an inductive constant in `extends`, got{indentExpr indExpr}"
      indNames := indNames.push indName.eraseMacroScopes
    let indVals ← indNames.mapM getConstInfoInduct
    let {levelParams, type := origType, numParams := baseNumParams,  ..} := indVals[0]!
    unless ← indVals[1:].allM (fun indVal => pure (indVal.levelParams == levelParams) <&&> isDefEq indVal.type origType) do
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
    let (type,_) ← modMap origType |>.run {} |>.run {map := map}
    unless !type.hasMVar do
    -- TODO this inductive translation is partial and requires the user to complete holes, this is not implemented yet.
      throwError "Failed to construct the type of the extended inductive: the translation generated holes. TODO expose a way to fill these holes."
    let expandedDeclId ← withRef? i do
      Term.expandDeclId (← getCurrNamespace) indVals[0]!.levelParams i {}
    let newShortIndName := expandedDeclId.shortName
    let newIndName := expandedDeclId.declName
    checkNotAlreadyDeclared newIndName
    Term.withDeclName newIndName do
    Term.withoutSavingRecAppSyntax do
    let (numParams, addedCtors) ←
      if declaredParams.size == 0 && baseNumParams > 0 then
        try
          pure (defaultNumParams, (← elabExtendedCtors newShortIndName newIndName levelParams type defaultNumParams ctors))
        catch _ =>
          pure (0, (← elabExtendedCtors newShortIndName newIndName levelParams type 0 ctors))
      else
        pure (defaultNumParams, (← elabExtendedCtors newShortIndName newIndName levelParams type defaultNumParams ctors))
    let auxInds := indNames.mapIdx fun i indName =>
        let auxIndName := newIndName.str s!"Aux_{i+1}"
        let addIndExt := IndExtension.addInd { indName }
        { newIndName := auxIndName, numParams, levelParams, origType, type, extension :=  addIndExt }
    let addCtorsExt := IndExtension.addCtors { lparams := levelParams
                                               indType := type
                                               addedCtors := addedCtors }
    let realInd := { newIndName, numParams, levelParams, origType, type, extension :=  addCtorsExt }
    return auxInds.toList ++ [realInd]
  | _ => throwUnsupportedSyntax

def mkSizeOfName (name : Name) : Name :=
  name ++ `_sizeOf_inst

def mkCtorElimTypeName (indName : Name) : Name :=
  Name.str indName "ctorElimType"

def mkNoConfusionTypeName (indName : Name) : Name :=
  Name.str indName "noConfusionType"

def mkNoConfusionName (indName : Name) : Name :=
  Name.str indName "noConfusion"

def mkInjName (ctorName : Name) : Name :=
  Name.str ctorName "inj"

def mkInjEqName (ctorName : Name) : Name :=
  Name.str ctorName "injEq"

def mkAuxMappingIfValid (oldName newName : Name) : ModularM Unit := do
  let env ← getEnv
  if env.contains oldName && env.contains newName then
    let (name, ext) ← mkAuxMapping oldName newName
    modifyMap (·.insert name ext)

def mkAuxMappings (mkAuxName : List (Name → Name)) (oldName newName : Name) : ModularM Unit :=
  mkAuxName.forM fun mkAuxName =>
    mkAuxMappingIfValid (mkAuxName oldName) (mkAuxName newName)

def mkRecMapping (oldRecName newRecName : Name): ModularM Unit := do
  let oldRecVal ← getConstInfoRec oldRecName
  let newRecVal ← getConstInfoRec newRecName
  let oldArgBVar (oldNumArgs i : Nat) : Expr := mkBVar (oldNumArgs - 1 - i)
  let holeBVar (oldNumArgs numExtras i : Nat) : Expr := mkBVar (oldNumArgs + (numExtras - 1 - i))
  let mut recArgs : Array Expr := #[]
  let numOldMotives := oldRecVal.numMotives
  let numNewMotives := newRecVal.numMinors - numOldMotives
  for i in [:numOldMotives] do
    recArgs := recArgs.push (oldArgBVar numOldMotives i)
  for i in [:numNewMotives] do
    recArgs := recArgs.push (holeBVar numOldMotives numNewMotives i)
  let numOldMinors := oldRecVal.numMinors
  let numNewMinors := newRecVal.numMinors - numOldMinors
  for i in [:numOldMinors] do
    recArgs := recArgs.push (oldArgBVar numOldMotives i)
  for i in [:numNewMinors] do
    recArgs := recArgs.push (holeBVar numOldMotives numNewMotives i)
  let numArgs := oldRecVal.numParams + oldRecVal.numMotives + oldRecVal.numMinors
  let numHoles := numNewMotives + numNewMinors
  let recExt : ModularExtension := {
    expr := mkAppN (mkConst newRecVal.name (oldRecVal.levelParams.map .param)) recArgs
    levelParams := oldRecVal.levelParams
    numArgs
    numHoles
  }
  modifyMap (·.insert oldRecVal.name recExt)

def ExtendedInd.addInductiveMappings (oldIndName? : Option Name) (extendedInductive : ExtendedInd): ModularM Unit := do
  let some oldIndName := oldIndName? | return
  let newIndName := extendedInductive.newIndName
  let newIndParams := extendedInductive.levelParams
  let newIndLevels := newIndParams.map Level.param
  let newRecName := mkRecName newIndName
  let indExtension := { expr := mkConst newIndName newIndLevels
                        levelParams := newIndParams
                        numArgs := 0
                        numHoles := 0 }
  modifyMap (·.insert oldIndName indExtension)
  let indVal ← getConstInfoInduct oldIndName
  for ctorName in indVal.ctors do
    let newCtorName := ctorName.replacePrefix oldIndName newIndName
    let ctorExt := { expr := mkConst newCtorName newIndLevels
                     levelParams := newIndParams
                     numArgs := 0
                     numHoles := 0 }
    modifyMap (·.insert ctorName ctorExt)
    mkAuxMappings [mkInjName, mkInjEqName, mkNoConfusionName] ctorName newCtorName
  let oldRecName := mkRecName oldIndName
  mkRecMapping oldRecName newRecName
  -- TODO `rec_on` is currently no handled correctly
  let mkAuxNames := [mkRecOnName, mkCasesOnName, mkCtorIdxName, mkCtorElimTypeName, mkCtorElimName, mkNoConfusionTypeName, mkNoConfusionName, mkBelowName, mkBRecOnName, mkSizeOfName]
  mkAuxMappings mkAuxNames oldIndName newIndName

-- TODO add `addTermInfo'` for inductive/ctor names
@[modular_elab modular_inductive, incremental]
meta def elabExtendedInductive : ModularElab := fun stx => liftModularM do
  let extendedInds ← elabExtendedInd (← getMap) stx
  let mut oldIndName? := none
  let mut oldCtors := []
  for extendedInd in extendedInds do
    let newIndName := extendedInd.newIndName
    trace[Modular.Elab] m!"modMap : {(← getMap).toList}"
    let extendedInductive ← extendedInd.toInductiveView oldCtors
    oldCtors := extendedInductive.ctors
    trace[Modular.Elab] m!"extendedInductive ctors : {extendedInductive.ctors.map Constructor.type}"
    addDecl (.inductDecl extendedInd.levelParams extendedInd.numParams [extendedInductive] false)
    mkRecOn newIndName
    mkCasesOn newIndName
    mkCtorIdx newIndName
    mkCtorElim newIndName
    mkNoConfusion newIndName
    mkBelow newIndName
    mkBRecOn newIndName
    mkSizeOfInstances newIndName
    IndPredBelow.mkBelow newIndName
    mkInjectiveTheorems newIndName
    extendedInd.addInductiveMappings oldIndName?
    oldIndName? := some newIndName
