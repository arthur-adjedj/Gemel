import LeanALaCarte

inductive Var where
  | var : Nat → Var

inductive Lam where
  | lam : Lam → Lam
  | app : Lam → Lam → Lam

-- set_option trace.Modular.Elab true
modular STLC

mod inductive STLC extends Lam, Var

  /--
info: inductive STLC : Type
number of parameters: 0
constructors:
STLC.lam : STLC → STLC
STLC.app : STLC → STLC → STLC
STLC.var : Nat → STLC
-/
#guard_msgs in
#print STLC
