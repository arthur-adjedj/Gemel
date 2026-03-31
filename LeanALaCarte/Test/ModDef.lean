import LeanALaCarte.ModDef
import LeanALaCarte.ExtendInd
import LeanALaCarte.CheckTranslation

namespace ModDefTests

def base (n : Nat) : Nat := Nat.succ n

modular
  mod_def base' extends base

-- example (n : Nat) : base' n = Nat.succ n := rfl

theorem t : True := trivial

modular

  #guard_msgs in
  mod_def bad extends t

def baseWrap (n : Nat) : Nat := base n

modular
  mod_def baseWrap' extends baseWrap

-- example (n : Nat) : baseWrap' n = Nat.succ n := rfl

def idNat (n : Nat) : Nat := n

def zeroNat : Nat := Nat.zero

def stepNat (n : Nat) : Nat := Nat.succ n

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α .zero
  | cons : α → Vec α n → Vec α n.succ

def Vec.append (v₁ : Vec α n) (v₂ : Vec α k) : Vec α (k.add n) :=
  match v₁ with
  | nil => v₂
  | cons (n := n) a v₁ => cons a (v₁.append v₂)
termination_by sizeOf v₁

modular
  inductive Natt extends Nat where
    | succ' : Natt → Natt
  set_option pp.match false
  set_option trace.Modular.Elab true
  set_option pp.universes true
  set_option trace.Modular.Subst true
  noncomputable mod_def Natt.add extends Nat.add where
    expose_names
    intro a
    exact (h.1 x_3).succ'

modular
  inductive Vecc (α : Type) extends Vec α where
    | cons'{n} : α → Vecc α n → Vecc α n.succ

  mod_def Vecc.append extends Vec.append where
    intro n a v _ _ b
    subst_vars
    apply Vecc.cons' a
    apply b ⟨n,v⟩
    decreasing_tactic

/--
info: ModDefTests.Vecc.append {α : Type} {n k : Nat} (v₁ : Vecc α n) (v₂ : Vecc α k) : Vecc α (k.add ⟨n, v₁⟩.1)
-/
#guard_msgs in
#check Vecc.append

example : Natt.add (Natt.succ' .zero) (Natt.succ' .zero) = Natt.zero.succ'.succ' := rfl

example : Natt.add k n.succ' = (Natt.add k n).succ' := by rfl
