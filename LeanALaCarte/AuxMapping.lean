import LeanALaCarte.Elab
open Lean Parser Elab Meta Command

def mkAuxTempMapping (oldName : Name) (newAuxFVar : Expr) : ModularM (Name × ModularExtension) := do
  let oldInfo ← getConstInfo oldName
  let oldNumArgs := oldInfo.type.getNumHeadForalls
  let newNumArgs := (← inferType newAuxFVar).getNumHeadForalls
  unless oldNumArgs <= newNumArgs do
    throwError m!"Unexpected auxiliary mapping arity from `{oldName}` to `{newAuxFVar}`\nThe new declaration has fewer arguments ({newNumArgs}) than the old one ({oldNumArgs})"
  let numExtraArgs := newNumArgs - oldNumArgs
  let oldArgBVar (i : Nat) : Expr := mkBVar (oldNumArgs - 1 - i)
  let holeBVar (i : Nat) : Expr := mkBVar (oldNumArgs + (numExtraArgs - 1 - i))
  let mut auxArgs : Array Expr := #[]
  for i in [:oldNumArgs] do
    auxArgs := auxArgs.push (oldArgBVar i)
  for i in [:numExtraArgs] do
    auxArgs := auxArgs.push (holeBVar i)
  let auxExt : ModularExtension := {
    translation := mkAppN newAuxFVar auxArgs
    levelParams := oldInfo.levelParams
    numArgs := oldNumArgs
    numHoles := numExtraArgs
  }
  return (oldName.eraseMacroScopes, auxExt)

def addAuxTempMapping (oldName : Name) (newAuxFVar : Expr) : ModularM Unit := do
  let (name,mapping) ← mkAuxTempMapping oldName newAuxFVar
  modify fun m => m.insert name mapping

def mkAuxMapping (oldName newName : Name) : ModularM (Name × ModularExtension) := do
  let oldInfo ← getConstInfo oldName
  let newInfo ← getConstInfo newName
  let oldNumArgs := oldInfo.type.getNumHeadForalls
  let newNumArgs := newInfo.type.getNumHeadForalls
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

def addAuxMapping (oldName newName : Name) : ModularM Unit := do
  let (name,mapping) ← mkAuxMapping oldName newName
  modify fun m => m.insert name mapping
