import LeanALaCarte.NewMap
import LeanALaCarte.ExtendInd
import LeanALaCarte.CheckTranslation

namespace ModDefTests

def base (n : Nat) : Nat := Nat.succ n

modular
  mod_def base' extends base by
    skip

example (n : Nat) : base' n = Nat.succ n := rfl

theorem t : True := trivial

modular
  /-- error: `mod_def` can only extend declarations defined with `def` -/
  #guard_msgs in
  mod_def bad extends t by
    skip

def baseWrap (n : Nat) : Nat := base n

modular
  mod_def baseWrap' extends baseWrap by
    skip

example (n : Nat) : baseWrap' n = Nat.succ n := rfl

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

modular
  inductive Natt extends Nat where
    | succ' : Natt → Natt

  mod_def idNatt extends idNat by
    skip

  mod_def zeroNatt extends zeroNat by
    skip

  mod_def stepNatt extends stepNat by
    skip

  mod_def Natt.add extends Nat.add by
    expose_names
    intro a ⟨h₁,_⟩
    exact (h₁ x_3).succ'

  inductive Vecc (α : Type) extends Vec α where
    | cons'{n} : α → Vecc α n → Vecc α n.succ'

  mod_def Vecc.append extends Vec.append by
    intro n a v₁ h₁ _ b
    subst_vars
    obtain ⟨b₁,_⟩ := b
    exact Vecc.cons' a b₁

example (n : Natt) : idNatt n = n := rfl

example : zeroNatt = Natt.zero := rfl

example (n : Natt) : stepNatt n = Natt.succ n := rfl

example : idNatt = (fun n : Natt => n) := rfl

example : stepNatt = (fun n : Natt => Natt.succ n) := rfl

example : Natt.add (Natt.succ' .zero) (Natt.succ' .zero) = Natt.zero.succ'.succ' := rfl

example : Natt.add k n.succ' =  (Natt.add k n).succ' := by rfl
