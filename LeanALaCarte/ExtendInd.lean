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

/- TODO extend structure to manage mutual types -/
structure ExtendedInd where
  newIndName : Name
  numParams : Nat
  levelParams : List Name
  origType : Expr
  type : Expr
  extension : IndExtension

def IndExtension.AddInd.modifyInductiveType (e : ExtendedInd) (indFVar : Expr) (tempIndExt : ModularExtension) (oldCtors : List Constructor)(addInd : AddInd): ModularM InductiveType := do
  let indVal ← getConstInfoInduct addInd.indName
  let inheritedCtors ← indVal.ctors.mapM getConstInfoCtor
  let tempMap := (← getMap).insert addInd.indName tempIndExt
  let tempMap := tempMap.insert e.newIndName tempIndExt
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
      name := ctor.name.replacePrefix ctor.induct .anonymous
      type := ctorType : Constructor
    }
  return { name := e.newIndName
           type := e.type
           ctors := oldCtors ++ inheritedCtors}

def IndExtension.AddCtors.modifyInductiveType (e : ExtendedInd) (oldCtors : List Constructor) (addCtors : AddCtors): ModularM InductiveType := do
  return { name := e.newIndName
           type := e.type
           ctors := oldCtors ++ addCtors.addedCtors.toList}

def IndExtension.modifyInductiveType (e : ExtendedInd) (indFVar : Expr) (tempIndExt : ModularExtension) (oldCtors : List Constructor) : IndExtension → ModularM InductiveType
  | .addCtors a => a.modifyInductiveType e oldCtors
  | .addInd a => a.modifyInductiveType e indFVar tempIndExt oldCtors

def ExtendedInd.toInductiveType (oldIndName? : Option Name) (oldCtors : List Constructor) (e : ExtendedInd) : ModularM InductiveType := do
  withLocalDeclD e.newIndName e.origType fun newIndFVar => do
    let .cdecl i fvarId u _ bi k := (← getLCtx).get! newIndFVar.fvarId! | unreachable!
    let mappedDecl := .cdecl i fvarId u e.type bi k
    withReader (·.addDecl mappedDecl) do
      let tempIndExt : ModularExtension := {
        expr := newIndFVar
        levelParams := []
        numArgs := 0
        numHoles := 0
      }
      let oldCtors ← (do
        let some oldIndName := oldIndName? | return oldCtors
        withModifyMap (·.insert oldIndName tempIndExt) do
          let newIndConst := mkConst e.newIndName (e.levelParams.map .param)
          oldCtors.mapM fun ctor => do
            let ctorType ← modMap ctor.type
            unless !ctorType.hasMVar do
              -- TODO this inductive translation is partial and requires the user to complete holes, this is not implemented yet.
              throwError "Failed to translate constructor {ctor.name}: the translation generated holes. TODO expose a way to fill these holes."
            let ctorType := ctorType.replace fun
              | .fvar fvarId =>
                if fvarId == newIndFVar.fvarId! then some newIndConst else none
              | _ => none
            return {
              name := ctor.name.replacePrefix oldIndName .anonymous
              type := ctorType : Constructor
            })
      e.extension.modifyInductiveType e newIndFVar tempIndExt oldCtors

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
            name := /- newIndName ++-/ ctorName
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
    unless indVals[1:].all (·.levelParams == levelParams) do
      throwError "Different level params between inductives being extended"
    -- TODO check that the modmapped type of each indval is DefEq
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

-- TODO this algorithm is too naive, and should ideally be type-directed to make everything work well.
def mkRecMapping (oldRecName newRecName : Name): ModularM Unit := do
  let oldRecVal ← getConstInfoRec oldRecName
  let newRecVal ← getConstInfoRec newRecName
  let numParams := oldRecVal.numParams
  assert! numParams = newRecVal.numParams
  let numOldMotives := oldRecVal.numMotives
  let numOldMinors := oldRecVal.numMinors
  let numNewMotives := newRecVal.numMotives - numOldMotives
  let numNewMinors := newRecVal.numMinors - numOldMinors
  let numArgs := numParams + numOldMotives + numOldMinors + 1
  let numHoles := numNewMotives + numNewMinors
  let mut recArgs : Array Expr := #[]
  for i in [:numParams + numOldMotives + numOldMinors] do
    recArgs := recArgs.push (mkBVar (numParams + numOldMotives + numOldMinors - i))
  for i in [:numHoles] do
    recArgs := recArgs.push (mkBVar (numParams + numOldMotives + numOldMinors + numHoles - i))
  recArgs := recArgs.push (mkBVar 0)
  let recExtExpr := mkAppN (mkConst newRecVal.name (oldRecVal.levelParams.map .param)) recArgs
  let recExt : ModularExtension := {
    expr := recExtExpr
    levelParams := oldRecVal.levelParams
    numArgs
    numHoles
  }
  trace[Modular.Elab] m!"rec extension: {oldRecVal.name} => {recExt}"
  modifyMap (·.insert oldRecVal.name recExt)

def addCtorsMappings (oldIndName : Name) (extendedInductive : ExtendedInd)  : ModularM Unit := do
  let newIndName := extendedInductive.newIndName
  let newIndParams := extendedInductive.levelParams
  let newIndLevels := newIndParams.map Level.param
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

def IndExtension.AddInd.addMappings (extendedInductive : ExtendedInd) (a : AddInd) : ModularM Unit := do
  let oldIndName := a.indName
  let newIndName := extendedInductive.newIndName
  addCtorsMappings oldIndName extendedInductive
  let newRecName := mkRecName newIndName
  let oldRecName := mkRecName oldIndName
  -- TODO this currently only works if the inductive getting extended is empty. Otherwise, the mapping is very much incorrect.
  mkRecMapping oldRecName newRecName
  -- TODO `rec_on` is currently no handled correctly
  let mkAuxNames := [mkRecOnName, mkCasesOnName, mkCtorIdxName, mkCtorElimTypeName, mkCtorElimName, mkNoConfusionTypeName, mkNoConfusionName, mkBelowName, mkBRecOnName, mkSizeOfName]
  mkAuxMappings mkAuxNames oldIndName newIndName

def ExtendedInd.addExtensionMappings (extendedInductive : ExtendedInd) : ModularM Unit :=
  match extendedInductive.extension with
    | .addInd a => a.addMappings extendedInductive
    | .addCtors _ => return

def ExtendedInd.addInductiveMappings (oldIndName? : Option Name) (extendedInductive : ExtendedInd): ModularM Unit := do
  extendedInductive.addExtensionMappings
  let some oldIndName := oldIndName? | return
  let newIndName := extendedInductive.newIndName
  addCtorsMappings oldIndName extendedInductive
  let newRecName := mkRecName newIndName
  let oldRecName := mkRecName oldIndName
  mkRecMapping oldRecName newRecName
  -- TODO `rec_on` is currently no handled correctly
  let mkAuxNames := [mkRecOnName, mkCasesOnName, mkCtorIdxName, mkCtorElimTypeName, mkCtorElimName, mkNoConfusionTypeName, mkNoConfusionName, mkBelowName, mkBRecOnName, mkSizeOfName]
  mkAuxMappings mkAuxNames oldIndName newIndName

meta def mkAuxConstructions (indName : Name) : MetaM Unit := do
  mkRecOn indName
  mkCasesOn indName
  mkCtorIdx indName
  mkCtorElim indName
  mkNoConfusion indName
  mkBelow indName
  mkBRecOn indName
  mkSizeOfInstances indName
  IndPredBelow.mkBelow indName
  mkInjectiveTheorems indName

meta def elabExtension (oldIndName? : Option Name) (oldCtors : List Constructor) (extendedInd : ExtendedInd) : ModularM (List Constructor) := do
  let newIndName := extendedInd.newIndName
  trace[Modular.Elab] m!"Elaborating extended inductive {extendedInd.newIndName}"
  let extendedInductive ← extendedInd.toInductiveType oldIndName? oldCtors
  -- In order to avoid name conflicts between ctors of auxiliary inductives, we first elaborate ctor names without a scope, then prepend said ctors with the right names
  let extendedInductive := {extendedInductive with ctors := extendedInductive.ctors.map fun ctor => {ctor with name := extendedInductive.name ++ ctor.name}}
  trace[Modular.Elab] m!"extendedInductive ctors : {extendedInductive.ctors.map Constructor.type}"
  addAndCompile (.inductDecl extendedInd.levelParams extendedInd.numParams [extendedInductive] false)
  compileDecls #[extendedInd.newIndName]
  mkAuxConstructions newIndName
  extendedInd.addInductiveMappings oldIndName?
  trace[Modular.Elab] m!"modMap : {(← getMap).toList}"
  return extendedInductive.ctors

-- TODO add `addTermInfo'` for inductive/ctor names
@[modular_elab modular_inductive, incremental]
meta def elabExtendedInductive : ModularElab := fun stx => liftModularM do
  let extendedInds ← elabExtendedInd (← getMap) stx
  let mut oldIndName? := none
  let mut oldCtors := []
  for extendedInd in extendedInds do
    oldCtors ← elabExtension oldIndName? oldCtors extendedInd
    oldIndName? := some extendedInd.newIndName

syntax bracketedExplicitBinder := "(" withoutPosition(binderIdent ppSpace ": " term) ")"

syntax (name := modular_addInd_ext) "inductive" "extension" ident " extends " ident: modular_command

@[modular_elab modular_addInd_ext, incremental]
meta def elabAddIndExt : ModularElab
  | `(modular_command|inductive extension $F extends $ind) => liftModularM do
    let indName ← resolveGlobalConstNoOverload ind
    let (declName, _) ← mkDeclName (← getCurrNamespace) {} F.getId
    if (← getIndFunctors).contains declName then
      throwError "Functor {declName} already declared"
    modifyIndFunctors (NameMap.insert · declName (.addInd { indName := indName }))
  | _ => throwUnsupportedSyntax

syntax "inductive " "extension " ident binderIdent ("where" ctor*): modular_command

syntax (name := modular_indctive_def) "inductive" ident ":=" ident ws ("$" ws ident)+ : modular_command
@[modular_elab modular_indctive_def, incremental]
meta def elabModInd : ModularElab
  | `(modular_command|inductive $ind := $F1 $[$ $i]*) => liftModularM do
    let (newIndName, _) ← mkDeclName (← getCurrNamespace) {} ind.getId
    let some oldIndStx := i.back?
      | throwError "Ill-formed functor application. Expected app of the form `F1 $ ... $ Fn $ I` where `Fi` are feature functors, and `I` an inductive type"
    let oldIndName ← realizeGlobalConstNoOverload oldIndStx
    let functorsIdents := i[:i.size-1].toArray.reverse.push F1
    let functorNames ← functorsIdents.mapM fun F => do
      let (declName, _) ← mkDeclName (← getCurrNamespace) {} F.getId
      return declName
    let functorMap ← getIndFunctors
    let functors ← functorNames.mapM fun F => do
      let some indExt := functorMap.find? F
        | throwError "Unknown feature functor {F}"
      pure indExt
    let newIndNames :=
      functorNames.mapIdx fun idx _ =>
        if idx = functorNames.size-1 then
          newIndName
        else
          newIndName.append (.mkSimple s!"_aux{idx}")
    trace[Modular.Elab] "indNames : {newIndNames}"
    let oldInd ← getConstInfoInduct oldIndName
    let mut oldCtors ← oldInd.ctors.mapM fun ctorName => do
      let ctor ← getConstInfoCtor ctorName
      let ctorType := ctor.type
      pure {
        name := ctor.name.replacePrefix ctor.induct .anonymous
        type := ctorType : Constructor
      }
    for idx in [:newIndNames.size], F in functors do
      let oldIndName := if idx = 0 then oldIndName else newIndNames[idx-1]!
      let oldInd ← getConstInfoInduct oldIndName
      let extendedInd := { newIndName := newIndNames[idx]!,
                           numParams := oldInd.numParams,
                           levelParams := oldInd.levelParams,
                           origType := oldInd.type,
                           type := (← modMap oldInd.type),
                           «extension» := F }
      oldCtors ← elabExtension oldIndName oldCtors extendedInd
  | _ => throwUnsupportedSyntax
