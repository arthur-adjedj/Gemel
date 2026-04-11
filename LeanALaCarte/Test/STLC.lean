import LeanALaCarte.ModMap
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ExtendInd
import LeanALaCarte.ModularCommand
import LeanALaCarte.ModDef

inductive List.Has : List α → α → Type where
  | head : List.Has (a::l) a
  | tail : List.Has l a → List.Has (b::l) a

inductive Ty where
  -- Needed to avoid issue `lean4#13364` (https://github.com/leanprover/lean4/issues/13364)
  | dummy

-- Not needed for the formalisation done here, but without it, the translation of recursors and other auxiliaries is currently fucked up..
set_option inductive.autoPromoteIndices false
inductive Var  : List Ty → Ty → Type
  | var (h : Γ.Has A) : Var Γ A

def Ren {T} (Γ Δ : List T) := ∀ A, Γ.Has A → Δ.Has A

def Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head => .head
  | _,.tail h => .tail (R _ h)

def Ren.wk : Ren Γ (A::Γ) := fun _ h => .tail h

def Var.wk (R : Ren Γ Δ) : Var Γ B → Var Δ B
  | var h => .var (R _ h)

def Var.Subst (Γ Δ : List Ty) := ∀ {A}, Γ.Has A → Var Δ A

def Var.subst (s : Var.Subst Γ Δ) : Var Γ A → Var Δ A
  | .var h => s h

inductive Var.Red : Var Γ A → Var Γ A → Prop where

modular
  inductive NatTy extends Ty where
    | nat

  inductive NatExt extends Var where
    | const : Nat → NatExt Γ .nat
    | plus : NatExt Γ .nat → NatExt Γ .nat → NatExt Γ .nat


  mod_def NatExt.wk extends Var.wk where
    match_1 R with
      | .const a => .const a
      | .plus a b => .plus (NatExt.wk R a) (NatExt.wk R b)

  mod_def NatExt.Subst extends Var.Subst

  mod_def NatExt.subst extends Var.subst where
    match_1 s with
      | .const a => .const a
      | .plus a b => .plus (NatExt.subst s a) (NatExt.subst s b)

  inductive NatExt.Red extends Var.Red where
    | plus_const : NatExt.Red (.plus (.const a) (.const b)) (.const (a + b))
    | plus_lhs : NatExt.Red a₁ a₂ → NatExt.Red (.plus a₁ b) (.plus a₂ b)
    | plus_rhs : NatExt.Red b₁ b₂ → NatExt.Red (.plus a b₁) (.plus a b₂)

modular
  inductive LamTy extends NatTy where
    | arr : LamTy → LamTy → LamTy

  inductive Term extends NatExt where
    | lam : Term (A::Γ) B → Term Γ (.arr A B)
    | app : Term Γ (.arr A B) → Term Γ A → Term Γ B

  mod_def Term.wk extends NatExt.wk where
    match_1 with
      | _, .lam f => .lam (Term.wk (Ren.ext R _) f)
      | _, .app a b => .app (Term.wk R a) (Term.wk R b)

  mod_def Term.Subst extends NatExt.Subst

  def Term.subst_ext (s : Term.Subst Γ Δ): ∀ {B}, (A::Γ).Has B → Term (A::Δ) B
    | _,.head => .var .head
    | _,.tail h => Term.wk Ren.wk (s h)

  def Term.subst_wk (a : Term Γ A) : Term.Subst (A::Γ) Γ
    | _,.head => a
    | _,.tail h => .var h

  mod_def Term.subst extends NatExt.subst where
    match_1 with
      | _, .lam f => .lam (Term.subst (Term.subst_ext s) f)
      | _, .app a b => .app (Term.subst s a) (Term.subst s b)

  inductive Term.Red extends NatExt.Red where
    | beta : Term.Red (.app (.lam f) x) (Term.subst (Term.subst_wk x) f)
    | lam : Term.Red f₁ f₂ → Term.Red (.lam f₁) (.lam f₂)
    | app_lhs : Term.Red f₁ f₂ → Term.Red (.app f₁ x) (.app f₂ x)
    | app_rhs : Term.Red x₁ x₂ → Term.Red (.app f x₁) (.app f x₂)
