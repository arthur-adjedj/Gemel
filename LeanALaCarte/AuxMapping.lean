import LeanALaCarte.Elab
open Lean Parser Elab Meta Command

def mkAuxMapping (oldName newName : Name) : TermElabM (Name × ModularExtension) := do
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
