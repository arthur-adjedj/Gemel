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
  origType : Expr
  type : Expr
  /-We ideally want extensions to extend arbitrary inductives family instantiations , not just the base case, e.g consider cases like:`inductive Foo (A) extends Prod A A where ...`.
  (Instantiating type parameters of the extended types here makes sense to me, instantiating indices not so much.)
  In practice, the toy system currently implemented simply maps from constant names to Exprs, so it wouldn't work for such cases. Instead, the real implementation will have to rely on something to unify patterns, e.g using `DiscrTree`s-/
  indNames : Array Name
  addedConstrs : Array Constructor

def ExtendedInd.toInductiveView (e : ExtendedInd) : ModularM InductiveType := do
  let indVals ← e.indNames.mapM getConstInfoInduct
  let inheritedCtors ← indVals.foldlM (init := []) fun acc indVal => do
    return (← indVal.ctors.mapM getConstInfoCtor) ++ acc
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
    let tempMap := e.indNames.foldl (init := ← getMap) fun acc indName =>
      acc.insert indName.eraseMacroScopes tempIndExt
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
def elabExtendedInd (map : ModularMap) (stx : Syntax) : TermElabM ExtendedInd := do
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
    let (numParams, addedConstrs) ←
      if declaredParams.size == 0 && baseNumParams > 0 then
        try
          pure (defaultNumParams, (← elabExtendedCtors newShortIndName newIndName levelParams type defaultNumParams ctors))
        catch _ =>
          pure (0, (← elabExtendedCtors newShortIndName newIndName levelParams type 0 ctors))
      else
        pure (defaultNumParams, (← elabExtendedCtors newShortIndName newIndName levelParams type defaultNumParams ctors))
    return { newIndName, numParams, levelParams, origType, type, indNames, addedConstrs }
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

def addInductiveMappings (extendedInductive : ExtendedInd) : ModularM Unit := do
  let newIndName := extendedInductive.newIndName
  let newIndParams := extendedInductive.levelParams
  let newIndLevels := newIndParams.map .param
  let newRecName := mkRecName newIndName
  let numAddedCtors := extendedInductive.addedConstrs.size
  let indExt : ModularExtension := { expr := mkConst newIndName newIndLevels
                                     levelParams := newIndParams
                                     numArgs := 0
                                     numHoles := 0 }
  for indName in extendedInductive.indNames do
    modifyMap (·.insert indName indExt)
    -- maps := (indName.eraseMacroScopes,indExt)::maps
    let indVal ← getConstInfoInduct indName
    for ctorName in indVal.ctors do
      let newCtorName := ctorName.replacePrefix indName newIndName
      let ctorExt : ModularExtension := { expr := mkConst newCtorName newIndLevels
                                          levelParams := newIndParams
                                          numArgs := 0
                                          numHoles := 0 }
      modifyMap (·.insert ctorName ctorExt)
      mkAuxMappings [mkInjName, mkInjEqName, mkNoConfusionName] ctorName newCtorName
    let oldRecName := mkRecName indName
    let oldRecVal ← getConstInfoRec oldRecName
    let oldNumArgs := oldRecVal.type.getNumHeadForalls
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
      expr := mkAppN (mkConst newRecName (oldRecVal.levelParams.map .param)) recArgs
      levelParams := oldRecVal.levelParams
      numArgs := oldNumArgs
      numHoles := numExtraMinors
    }
    modifyMap (·.insert oldRecName.eraseMacroScopes recExt)
    let mkAuxNames := [mkRecOnName, mkCasesOnName, mkCtorIdxName, mkCtorElimTypeName, mkCtorElimName, mkNoConfusionTypeName, mkNoConfusionName, mkBelowName, mkBRecOnName, mkSizeOfName]
    mkAuxMappings mkAuxNames indName newIndName

-- TODO add `addTermInfo'` for inductive/ctor names
@[modular_elab modular_inductive, incremental]
meta def elabExtendedInductive : ModularElab := fun stx => liftModularM do
  let extendedInd ← elabExtendedInd (← getMap) stx
  let newIndName := extendedInd.newIndName
  trace[Modular.Elab] m!"modMap : {(← getMap).toList}"
  let extendedInductive ← extendedInd.toInductiveView
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
  addInductiveMappings extendedInd
  -- TODO? add mappings for `SizeOf` and related ?
