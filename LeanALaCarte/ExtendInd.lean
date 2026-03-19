import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
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
  addedConstrs : Array Expr


def ExtendedInd.toInductiveView (map : ModularMap) (e : ExtendedInd) : MetaM InductiveType := do
  let indVals ← e.indNames.mapM getConstInfoInduct
  let ctors ← indVals.foldlM (init := []) fun acc indVal => do
    return (← indVal.ctors.mapM getConstInfoCtor) ++ acc
  let ctors ← ctors.mapM fun ctor =>
    return { name := ctor.name.replacePrefix ctor.induct e.newIndName
             type := ← modmap map ctor.type }
  return { name := e.newIndName
           type := e.type
           ctors := ctors }

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
    match e with
    | .forallE _ d b _ => visit d *> visit b
    | .lam _ d b _ => visit d *> visit b
    | .letE _ t v b _ => visit t *> visit v *> visit b
    | .app f a => visit f *> visit a
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => pure ()
  visit ctorType
  return ctorType

private def elabExtendedCtors (newIndName : Name) (indType : Expr) (numParams : Nat)
    (ctors : Array Syntax) : TermElabM (Array Expr) := do
  withLocalDeclD newIndName indType fun indFVar => do
    forallTelescopeReducing indType fun allArgs _ => do
      let params := allArgs.extract 0 numParams
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
              mkForallFVars params type

syntax (name := modular_inductive) "inductive" ident "extends" ident,+ "where" ctor* :  modular_command

def elabExtendedInd (stx : Syntax) : TermElabM ExtendedInd := do
  match stx with
  | `(modular_command|inductive $i extends $inds,* where $ctors*) => do
    let newIndName ← resolveGlobalConstNoOverload i
    let indNames ← inds.getElems.mapM resolveGlobalConstNoOverload
    let indVals ← indNames.mapM getConstInfoInduct
    let {levelParams, type, numParams,  ..} := indVals[0]!
    unless ← indVals[1:].allM (fun indVal => pure (indVal.levelParams == levelParams) <&&> isDefEq indVal.type type) do
      throwError "invalid types between inductives being extended"
    let addedConstrs ← elabExtendedCtors newIndName type numParams ctors
    return { newIndName, numParams, levelParams, type, indNames, addedConstrs }
  | _ => throwUnsupportedSyntax

@[modular_elab modular_inductive]
def elabExtendedInductive : ModularElab := fun stx => do
  let map ← get
  liftTermElabM do
    let extendedInd ← elabExtendedInd stx
    let extendedInductive ← extendedInd.toInductiveView map
    addDecl (.inductDecl extendedInd.levelParams extendedInd.numParams [extendedInductive] false)
    -- TODO various mkAuxConstructions
  -- TODO add relevant stuff to the modmap
  -- addInductiveMappings map extendedInductive
