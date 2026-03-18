import LeanALaCarte.Basic
open Lean Elab Meta Command


/-- Bundle of the various syntax elements of an extended inductive, to be elaborated as an `ExtendedInd` later -/
structure ExtendedIndView where
  -- TODO
  -- notes: Don't forget to include things like attributes, check what's in `InductiveView` and what should/shouldn't be kept/used here.
  -- One current limitation is that Lean does not record what attributes where applied to a given declaration, so copying/adapting the

/- TODO extend structure to manage mutual types -/
structure ExtendedInd where
  newIndName : Name
  levelParams : List Name
  type : Expr
  /-We ideally want extensions to extend arbitrary inductives family instantiations , not just the base case, e.g consider cases like:`inductive Foo (A) extends Prod A A where ...`.
  (Instantiating type parameters of the extended types here makes sense to me, instantiating indices not so much.)
  In practice, the toy system currently implemented simply maps from constant names to Exprs, so it wouldn't work for such cases. Instead, the real implementation will have to rely on something to unify patterns, e.g using `DiscrTree`s-/
  indNames : List Name
  addedConstrs : Array Expr

def ExtendedInd.toInductiveView (e : ExtendedInd) : ModularM InductiveType := do
  let indVals ← e.indNames.mapM getConstInfoInduct
  --TODO check all extended inds have the same type signature
  let ctors ← indVals.flatMapM (·.ctors.mapM getConstInfoCtor)
  let ctors ← ctors.mapM fun ctor =>
    return { name := ctor.name.replacePrefix ctor.induct e.newIndName
             type := ← modmap ctor.type }
  return { name := e.newIndName
           type := e.type
           ctors := ctors }

/- TODO
  - Make syntax for inductive extension
  - Add translation of ind type, ind constrs and ind recursors to the modular map
  - Experiment with adding translation for auxiliary defs too
-/
