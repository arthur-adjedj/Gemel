import LeanALaCarte.Basic
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ExtendInd
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
    |>.insert (``Nat).eraseMacroScopes ⟨q(Natt),[], 0, 0⟩
    |>.insert (``Nat.zero).eraseMacroScopes ⟨q(Natt.zero),[],0,0⟩
    |>.insert (``Nat.succ).eraseMacroScopes ⟨mkApp q(Natt.succ) (mkBVar 0),[],1,0⟩
    |>.insert (``Nat.rec).eraseMacroScopes ⟨mkApp5 (mkConst ``Natt.rec [.param `u]) (mkBVar 3) (mkBVar 2) (mkBVar 1) (mkBVar 4) (mkBVar 0),[`u],4,1⟩

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

namespace test2

-- set_option trace.Modular.Elab true
-- set_option trace.Modular.Subst true
modular
  inductive Natt extends Nat where
    | succ' : Natt → Natt

modular
  /-- info: Natt.succ' : Natt → Natt -/
  #guard_msgs in
  #check Natt.succ'

modular
  /-- info: Nat -/
  #guard_msgs (check info) in
  set_option pp.universes true in
  #check_translation Nat

modular
  inductive Natt2 extends Nat where
    | succ' : Natt2 → Natt2
  /-- info: Natt2 -/
  #guard_msgs in
  #check_translation Nat

end test2

namespace test3

-- Parameterized type with an extra constructor (result type inferred).
modular
  inductive OptionExt extends Option where
    | extra

-- Another parameterized type with an extra constructor.
modular
  inductive ListExt extends List where
    | extra

-- Indexed families currently test shape/support best without new constructors.
modular
  inductive EqExt extends Eq where

modular
  inductive VectorExt extends Vector where

end test3

namespace test4

inductive Var (α : Type) where
  | var : α → Var α

modular
  inductive Term' (α : Type) extends Var α where
    | lam : Term' α → Term' α
    | app : Term' α → Term' α → Term' α

/-- info: Term' (α : Type) : Type -/
#guard_msgs in
#check Term'
/-- info: Term'.var {α : Type} : α → Term' α -/
#guard_msgs in
#check Term'.var
/-- info: Term'.lam {α : Type} : Term' α → Term' α -/
#guard_msgs in
#check Term'.lam
/-- info: Term'.app {α : Type} : Term' α → Term' α → Term' α -/
#guard_msgs in
#check Term'.app
end test4

namespace test5

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty

abbrev Env := List Ty

set_option inductive.autoPromoteIndices false in --Fails otherwise, should it not ?
inductive Var : (Γ : Env) → Ty → Type
  | var {Γ t} (n : Nat) (h : Γ[n]? = some t) : Var Γ t

modular
  inductive Term extends Var where
    | lam : Term (A::Γ) B → Term Γ (.arr A B)
    | app : Term Γ (.arr A B) → Term Γ A → Term Γ B

end test5
