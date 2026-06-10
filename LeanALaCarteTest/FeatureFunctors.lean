import LeanALaCarte

inductive Var where
  | var : Nat → Var

inductive Lam where
  | lam : Lam → Lam
  | app : Lam → Lam → Lam

modular
  inductive extension VarF extends Var

  inductive extension LamF extends Lam

  inductive STLC := LamF $ VarF $ Empty

  #print STLC
