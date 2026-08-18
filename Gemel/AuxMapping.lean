module

public import Gemel.Elab
public meta import Lean.Meta.Eqns
public meta import Lean.Meta.Match.MatchEqsExt
public meta import Gemel.Elab
public import Lean.Meta.Match.MatchEqsExt
public import Gemel.ModMap

public meta section --TODO be less public

open Lean Parser Elab Meta Command

/-- This function does **not** check for the correctness of the translation, which may lead to the construction of ill-formed terms through ill-defined translations. Furthermore, the algorithm is very naive in that it simply decides the "holes" are the extra args at the end of the forall telescope, rather than be name/type-directed.
TODO proper checks and smarter algorithm here. -/
def mkAuxMapping (oldName newName : Name) : ModularM (Name × ModularExtension) := do
  let oldInfo ← getConstInfo oldName
  let newInfo ← getConstInfo newName
  let oldNumArgs := oldInfo.type.getNumHeadForalls
  let newNumArgs := newInfo.type.getNumHeadForalls
  unless oldNumArgs <= newNumArgs do
    throwError m!"Unexpected auxiliary mapping arity from `{oldName}` to `{newName}`\nThe new declaration :{indentExpr newInfo.type} \n has fewer arguments ({newNumArgs}) than the old one ({oldNumArgs}) {indentExpr oldInfo.type}"
  let numExtraArgs := newNumArgs - oldNumArgs
  let oldArgBVar (i : Nat) : Expr := mkBVar (oldNumArgs - 1 - i)
  let holeBVar (i : Nat) : Expr := mkBVar (oldNumArgs + (numExtraArgs - 1 - i))
  let mut auxArgs : Array Expr := #[]
  for i in [:oldNumArgs] do
    auxArgs := auxArgs.push (oldArgBVar i)
  for i in [:numExtraArgs] do
    auxArgs := auxArgs.push (holeBVar i)
  let auxExt : ModularExtension := {
    expr := mkAppN (mkConst newName (oldInfo.levelParams.map .param)) auxArgs
    levelParams := oldInfo.levelParams
    numArgs := oldNumArgs
    numHoles := numExtraArgs
  }
  return (oldName.eraseMacroScopes, auxExt)

def addAuxMapping (oldName newName : Name) : ModularM Unit := do
  let (name,mapping) ← mkAuxMapping oldName newName
  trace[Modular.Elab] m!"Adding mapping {oldName} ⇒ {mapping}"
  addMapEntry name mapping

def addUnfoldEqMapping (oldName newName : Name) : ModularM Unit := do
  let some oldEqn ← getUnfoldEqnFor? oldName true | return
  let some newEqn ← getUnfoldEqnFor? newName true | return
  trace[Modular.Elab] "oldEqns : {oldEqn}"
  trace[Modular.Elab] "newEqns : {newEqn}"
  addAuxMapping oldEqn newEqn

def mapOldToNewEqnLemmas (oldName newName : Name) : ModularM (Option (AssocList Name Name)) := do
  let mut some oldEqns ← getEqnsFor? oldName | return none
  let mut some newEqns ← getEqnsFor? newName | return none
  let mut res := AssocList.empty
  for i in [:oldEqns.size] do
    for j in [:newEqns.size] do
      if (← areCompatible oldEqns[i]! newEqns[j]!) then
        res := res.cons oldEqns[i]! newEqns[j]!
  return res
where
  areCompatible (oldEqnName newEqnName : Name) : ModularM Bool := do
    let oldEqn ← getConstInfo oldEqnName
    let newEqn ← getConstInfo newEqnName
    let oldTy ← modMap oldEqn.type
    let newTy := newEqn.type
    let (_,_,oldTy) ← forallMetaTelescopeReducing oldTy
    let (_,_,newTy) ← forallMetaTelescopeReducing newTy
    withTransparency .none (isDefEq oldTy newTy)

def mapOldToNewMatch (oldName newName : Name) : ModularM (Option (AssocList Name Name)) := do
  let mut ⟨oldEqns,oldSplitter,_⟩ ← Match.getEquationsFor oldName
  let mut ⟨newEqns,newSplitter,_⟩ ← Match.getEquationsFor newName
  let mut res := AssocList.empty.insert oldSplitter newSplitter
  for i in [:oldEqns.size] do
    for j in [:newEqns.size] do
      if (← mapOldToNewEqnLemmas.areCompatible oldEqns[i]! newEqns[j]!) then
        res := res.cons oldEqns[i]! newEqns[j]!
  return res

def addEqnMappings (oldName newName : Name) : ModularM Unit := do
  let some eqnMappings ← mapOldToNewEqnLemmas oldName newName | return
  for (oldEqn, newEqn) in eqnMappings do
    addAuxMapping oldEqn newEqn

def addMatchMappings (oldName newName : Name) : ModularM Unit := do
  let some eqnMappings ← mapOldToNewMatch oldName newName | return
  for (oldEqn, newEqn) in eqnMappings do
    addAuxMapping oldEqn newEqn
