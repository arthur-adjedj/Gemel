module


public section

def Array.mkM [Monad m] (n : Nat) (k : m α) : m (Array α) := do
  let mut arr := Array.emptyWithCapacity n
  for _ in [0:n] do
    arr := arr.push (← k)
  return arr
