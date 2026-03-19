import LeanALaCarte.Basic
import Lean.Meta.Check
import Qq
open Qq
open Lean Meta Elab Command Term

namespace tests
-- Natural numbers extended with a second "succ" branch
inductive Natt : Type where
  | zero
  | succ : Natt → Natt
  | succ' : Natt → Natt

-- We encode a "partial map" from `Nat` to `Natt` manually here, the objective later is to generate those (and more, e.g for `below`, `recOn`, `brecOn` etc) automatically.
def testmap : ModularMap :=
  Std.HashMap.emptyWithCapacity 0
    |>.insert ``Nat ⟨q(Natt),[], 0, 0⟩
    |>.insert ``Nat.zero ⟨q(Natt.zero),[],0,0⟩
    |>.insert ``Nat.succ ⟨mkApp q(Natt.succ) (mkBVar 0),[],1,0⟩
    |>.insert ``Nat.rec ⟨mkApp5 (mkConst ``Natt.rec [.param `u]) (mkBVar 3) (mkBVar 2) (mkBVar 1) (mkBVar 4) (mkBVar 0),[`u],4,1⟩

elab "#partial_map" e:term : command =>
  liftTermElabM do
    let e ← elabTerm e none
    let mapped_term ← modmap testmap e
    logInfo m!"{mapped_term}"

set_option pp.mvars.levels false

set_option pp.funBinderTypes true
/-- info: Natt -/
#guard_msgs in
#partial_map Nat
/-- info: Natt.zero -/
#guard_msgs in
#partial_map Nat.zero
/-- info: fun (n : Natt) => n.succ -/
#guard_msgs in
#partial_map Nat.succ
/--
info: fun {motive : Natt → Sort _} (zero : motive Natt.zero) (succ : (n : Natt) → motive n → motive n.succ) (t : Natt) =>
  Natt.rec zero succ (?m.3 zero succ t) t
-/
#guard_msgs in
#partial_map @Nat.rec

end tests
