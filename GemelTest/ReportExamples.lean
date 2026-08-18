import Gemel

inductive Var where
  | var : Nat → Var

def is_var_zero : Var → Bool
  | .var 0     => true
  | .var (_+1) => false

def Var.repr : Var → String
  | var n => s!"#{n}"

theorem is_var_zero_eq (t : Var) (h : is_var_zero t) : t = .var 0 := by
  cases t with
  | var n =>
    cases n with
    | zero => rfl
    | succ _ => nomatch h

modular Term

mod inductive Term extends Var where
  | lam : Term → Term
  | app : Term → Term → Term

mod def Term.is_var_zero extends is_var_zero where
  extend match_1 with
    | .app _ _ => false
    | .lam _   => false

mod def Term.repr extends Var.repr where
  extend match_1 with
  | .app f x => s!"{Term.repr f} {Term.repr x}"
  | .lam f => s!"λ {Term.repr f}"
termination_by structural t => t
