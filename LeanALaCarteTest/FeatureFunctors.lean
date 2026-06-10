import LeanALaCarte

inductive Var where
  | var : Nat → Var

inductive Lam where
  | lam : Lam → Lam
  | app : Lam → Lam → Lam

-- set_option trace.Modular.Elab true
modular
  inductive extension VarF extends Var

  inductive extension LamF extends Lam

  inductive STLC := LamF $ Var

  #print STLC
