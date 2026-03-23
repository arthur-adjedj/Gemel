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
    intro _ ⟨h₁,_⟩
    exact h₁ x_3.succ'

example (n : Natt) : idNatt n = n := rfl

example : zeroNatt = Natt.zero := rfl

example (n : Natt) : stepNatt n = Natt.succ n := rfl

example : idNatt = (fun n : Natt => n) := rfl

example : stepNatt = (fun n : Natt => Natt.succ n) := rfl

example : Natt.add (Natt.succ' .zero) (Natt.succ' .zero) = Natt.zero.succ'.succ' := rfl
#check Natt
