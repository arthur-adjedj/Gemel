module

public import Gemel.ModMap
public import Gemel.CheckTranslation
public import Gemel.ExtendInd
public import Gemel.ModDef
public import Gemel.ModularCommand
public import Lean.Meta.Check
public import Qq

public section

open Qq
open Lean Meta Elab Command Term

namespace tests
-- Natural numbers extended with a second "succ" branch
inductive Natt : Type where
  | zero
  | succ : Natt → Natt
  | succ' : Natt → Natt

-- We encode a "partial map" from `Nat` to `Natt` manually here, the objective later is to generate those (and more, e.g for `below`, `recOn`, `brecOn` etc) automatically.
meta def testmap : ModularMap :=
  Std.HashMap.emptyWithCapacity 0
    |>.insert (``Nat).eraseMacroScopes ⟨mkConst ``Natt,[], 0, 0⟩
    |>.insert (``Nat.zero).eraseMacroScopes ⟨mkConst ``Natt.zero,[],0,0⟩
    |>.insert (``Nat.succ).eraseMacroScopes ⟨mkApp (mkConst ``Natt.succ) (mkBVar 0),[],1,0⟩
    |>.insert (``Nat.rec).eraseMacroScopes ⟨mkApp5 (mkConst ``Natt.rec [.param `u]) (mkBVar 3) (mkBVar 2) (mkBVar 1) (mkBVar 4) (mkBVar 0),[`u],4,1⟩

elab "#partial_map" e:term : command =>
  liftTermElabM do
    let e ← elabTerm e none
    let (mapped_term,_) ← modMap e |>.run {} |>.run {map := testmap}
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
  Natt.rec zero succ ?m.2 t
-/
#guard_msgs in
#partial_map @Nat.rec

end tests

namespace test2

-- set_option trace.Modular.Elab true
-- set_option trace.Modular.Subst true
modular test
  mod inductive Natt' extends Nat where
    | succ' : Natt' → Natt'
modular end test

modular test'
/-- info: test2.Natt'.succ' : Natt' → Natt' -/
#guard_msgs in
#check Natt'.succ'
modular end test'

modular test''
/-- info: Nat -/
#guard_msgs in
#check_translation Nat
modular end test''

modular test'''
mod inductive Natt2 extends Nat where
  | succ' : Natt2 → Natt2
/-- info: Natt2 -/
#guard_msgs in
#check_translation Nat
modular end test'''

end test2

namespace test3

-- Parameterized type with an extra constructor (result type inferred).
modular optionExt
mod inductive OptionExt extends Option where
  | extra
modular end optionExt

-- Another parameterized type with an extra constructor.
modular listExt
mod inductive ListExt extends List where
  | extra
modular end listExt

-- Indexed families currently test shape/support best without new constructors.
modular eqExt
mod inductive EqExt extends Eq where
modular end eqExt

modular vecExt
mod inductive VectorExt extends Vector where
modular end vecExt
end test3

namespace test4

inductive Var (α : Type) where
  | var : α → Var α

modular term'
mod inductive Term' (α : Type) extends Var α where
  | lam : Term' α → Term' α
  | app : Term' α → Term' α → Term' α

/-- info: test4.Term' (α : Type) : Type -/
#guard_msgs in
#check Term'
/-- info: test4.Term'.var {α : Type} : α → Term' α -/
#guard_msgs in
#check Term'.var
/-- info: test4.Term'.lam {α : Type} : Term' α → Term' α -/
#guard_msgs in
#check Term'.lam
/-- info: test4.Term'.app {α : Type} : Term' α → Term' α → Term' α -/
#guard_msgs in
#check Term'.app
modular end term'
end test4

namespace test5

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty

abbrev Env := List Ty

set_option inductive.autoPromoteIndices false in --Fails otherwise, should it not ?
inductive Var : (Γ : Env) → Ty → Type
  | var {Γ A} (h : A ∈ Γ) : Var Γ A

def Ren (Γ Δ : Env) := ∀ A, A ∈ Γ → A ∈ Δ

theorem Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head _ => .head _
  | _,.tail _ h => .tail _ (R _ h)

def Var.wk (R : Ren Γ Δ) : Var Γ B → Var Δ B
  | var h => .var (R _ h)
set_option pp.match false in


modular term
  mod inductive Term extends Var where
    | lam : Term (A::Γ) B → Term Γ (.arr A B)
    | app : Term Γ (.arr A B) → Term Γ A → Term Γ B
