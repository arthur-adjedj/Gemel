module

public import LeanALaCarte.ModMap
public import LeanALaCarte.CheckTranslation
public import LeanALaCarte.ExtendInd
public import LeanALaCarte.ModularCommand
public import LeanALaCarte.ModDef

public section

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty

abbrev Env := List Ty

set_option inductive.autoPromoteIndices false in --Fails otherwise, should it not ?
inductive Var : (Γ : Env) → Ty → Type
  | var {Γ A} (h : A ∈ Γ) : Var Γ A

def Ren (Γ Δ : Env) := ∀ A, A ∈ Γ → A ∈ Δ

def Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head _ => .head _
  | _,.tail _ h => .tail _ (R _ h)

def Var.wk (R : Ren Γ Δ) : Var Γ B → Var Δ B
  | var h => .var (R _ h)

modular
  inductive Term extends Var where
    | lam : Term (A::Γ) B → Term Γ (.arr A B)
    | app : Term Γ (.arr A B) → Term Γ A → Term Γ B

  mod_def Term.wk extends Var.wk where
    match_1 with
      | .lam f => .lam (f.wk (Ren.ext R _))
      | .app a b => .app (a.wk R) (b.wk R)
