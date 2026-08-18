module
public import Lean.Elab.Term.TermElabM

public section

def Array.mkM [Monad m] (n : Nat) (k : m α) : m (Array α) := do
  let mut arr := Array.emptyWithCapacity n
  for _ in [0:n] do
    arr := arr.push (← k)
  return arr

def Lean.Elab.Term.withDeclName' [Monad m] [MonadControlT TermElabM m] (name : Name) (k1 : m α) :
m α := do
  control (m := TermElabM) fun k2 => do
    Term.withDeclName name (k2 k1)
