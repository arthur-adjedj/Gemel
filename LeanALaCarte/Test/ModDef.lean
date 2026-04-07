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

def Nat.add' (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => (Nat.add' n k).succ


modular
  inductive Natt extends Nat where
    | succ' : Natt → Natt

   def Natt.add : Natt → Natt → Natt := fun _ x => match x with
      | .zero
      | .succ _
      | .succ' _ => .zero

  mod_def Natt.add' extends Nat.add' where
    expose_names
    exact match x with
      | .zero => n
      | .succ k => (Natt.add' n k).succ
      | .succ' k => (Natt.add' n k).succ'
  -- termination_by _ x => x

modular
  inductive Vecc (α : Type) extends Vec α where
    | cons'{n} : α → Vecc α n → Vecc α n.succ

  mod_def Vecc.append extends Vec.append where
    sorry

/--
info: ModDefTests.Vecc.append {α : Type} {n k : Nat} (v₁ : Vecc α n) (v₂ : Vecc α k) : Vecc α (k.add ⟨n, v₁⟩.1)
-/
#guard_msgs in
#check Vecc.append

example : Natt.add (Natt.succ' .zero) (Natt.succ' .zero) = Natt.zero.succ'.succ' := rfl

example : Natt.add k n.succ' = (Natt.add k n).succ' := by rfl
