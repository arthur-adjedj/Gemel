
import LeanALaCarte.ModDef
import LeanALaCarte.ExtendInd
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ModularCommand
import Lean

open Lean Elab Command Meta
public section

namespace ModDefTests

def base (n : Nat) : Nat := Nat.succ n

modular foo
  mod def base' extends base
modular end foo

example (n : Nat) : base' n = Nat.succ n := rfl

theorem t : True := trivial

modular bar

  mod def bad extends t
modular end bar

def baseWrap (n : Nat) : Nat := base n

modular baz
  mod def baseWrap' extends baseWrap
modular end baz
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
termination_by sizeOf v₁

def Nat.add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
termination_by structural _ x => x

def Nat.add' (n : Nat) : Nat → Nat := match n with
  | .zero => id
  | .succ n => fun k => (Nat.add' n k).succ

modular natt
  mod inductive Natt extends Nat where
    | succ' : Natt → Natt

  def Natt.add : Natt → Natt → Natt := fun n x => match x with
      | .zero => .zero
      | .succ x  => Natt.add n x |>.succ
      | .succ' x => Natt.add n x |>.succ'

  mod def Natt.add'' extends Nat.add' where
    matcher match_1 with
      | Natt.succ' n => fun k => (Natt.add'' n k).succ'

  mod def Natt.add' extends Nat.add where
    matcher match_1 with
      | n, Natt.succ' k => (Natt.add' n k).succ'
  termination_by structural _ x => x
modular end natt

modular vecc
  mod inductive Vecc (α : Type) extends Vec α where
    | cons'{n} : α → Vecc α n → Vecc α n.succ

  mod def Vecc.append extends Vec.append where
    matcher match_1 with
      | Nat.succ _,Vecc.cons' hd tl => Vecc.cons' hd (Vecc.append tl v₂)

/--
info: ModDefTests.Vecc.append {α : Type} {n k : Nat} (v₁ : Vecc α n) (v₂ : Vecc α k) : Vecc α (k.add n)
-/
#guard_msgs in
#check Vecc.append

/-- info: Natt.zero.succ'.succ' -/
#guard_msgs in
#reduce Natt.add' (Natt.succ' .zero) (Natt.succ' .zero)

/-- info: Natt.zero.succ'.succ' -/
#guard_msgs in
#reduce Natt.add'' (Natt.succ' .zero) (Natt.succ' .zero)

example : Natt.add k n.succ' = (Natt.add k n).succ' := by rfl
