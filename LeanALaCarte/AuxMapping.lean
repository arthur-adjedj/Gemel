module

public meta import LeanALaCarte.Elab
public import LeanALaCarte.Elab

public meta section

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

end
