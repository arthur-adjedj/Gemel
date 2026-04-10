module

public import LeanALaCarte.ModMap
public import LeanALaCarte.CheckTranslation
public import LeanALaCarte.ExtendInd
public import LeanALaCarte.ModularCommand
public import LeanALaCarte.ModDef

public section

inductive Ty where

set_option trace.Meta.Match.matchEqs true

set_option inductive.autoPromoteIndices false in --Fails otherwise, should it not ?
inductive Var : (Γ : List Ty) → Ty → Type
  | var {Γ A} (h : Γ.Mem A) : Var Γ A

def Ren {T} (Γ Δ : List T) := ∀ A, Γ.Mem A → Δ.Mem A

def Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head _ => .head _
  | _,.tail _ h => .tail _ (R _ h)

def Var.wk (R : Ren Γ Δ) : Var Γ B → Var Δ B
  | var h => .var (R _ h)

def Var.subst (s : ∀ {A}, Γ.Mem A → Var Δ A) : Var Γ A → Var Δ A
  | .var h => s h

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

  -- mod_def NatExt.subst extends Var.subst where
    -- match_1 s with
      -- | .const a => .const a
      -- | .plus a b => .plus (a.subst s) (b.subst s)


modular
  inductive LamTy extends NatTy where
    | arr : LamTy → LamTy → LamTy

  inductive Term extends NatExt where
    | lam : Term (A::Γ) B → Term Γ (.arr A B)
    | app : Term Γ (.arr A B) → Term Γ A → Term Γ B

  mod_def Term.wk extends NatExt.wk where
    foo with
      | .lam f => .lam (f.wk (Ren.ext R _))
      | .app a b => .app (a.wk R) (b.wk R)

  -- def Term.subst_ext {} (s : ∀ {A}, Γ.Mem A → Term Δ A)

  -- mod_def Term.subst extends NatExt.subst where
    -- match_1 with
      -- | .lam f => sorry
      -- | .app a b => .app (a.subst s) (b.subst s)
