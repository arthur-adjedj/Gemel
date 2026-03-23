import LeanALaCarte.NewMap
import LeanALaCarte.ExtendInd
import LeanALaCarte.CheckTranslation

namespace modDefTests

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

namespace inductiveExtension

def idNat (n : Nat) : Nat := n

def zeroNat : Nat := Nat.zero

def stepNat (n : Nat) : Nat := Nat.succ n

set_option pp.match false
set_option pp.funBinderTypes true
#print Nat.add
modular
  inductive Natt extends Nat where
    | succ' : Natt → Natt

  mod_def idNatt extends idNat by
    skip

  mod_def zeroNatt extends zeroNat by
    skip

  mod_def stepNatt extends stepNat by
    skip
  set_option trace.Modular.Elab true in
  set_option trace.Modular.Subst true in
  mod_def addNatt extends Nat.add by
    intro a ⟨h₁,h₂⟩

  set_option pp.funBinderTypes true
  -- #print addNatt.match_1
  #print Nat.add
  #check_translation @Nat.casesOn
  #check_translation Nat.add.match_1

example (n : Natt) : idNatt n = n := rfl

example : zeroNatt = Natt.zero := rfl

example (n : Natt) : stepNatt n = Natt.succ n := rfl

example : idNatt = (fun n : Natt => n) := rfl

example : stepNatt = (fun n : Natt => Natt.succ n) := rfl

example : addNatt Natt.zero Natt.zero = Natt.zero := rfl

end inductiveExtension

end modDefTests
