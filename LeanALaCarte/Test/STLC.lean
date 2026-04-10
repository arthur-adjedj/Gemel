module

public import LeanALaCarte.ModMap
public import LeanALaCarte.CheckTranslation
public import LeanALaCarte.ExtendInd
public import LeanALaCarte.ModularCommand
public import LeanALaCarte.ModDef

public section

inductive List.Has : List α → α → Type where
  | head : List.Has (a::l) a
  | tail : List.Has l a → List.Has (b::l) a

inductive Ty where

set_option inductive.autoPromoteIndices false in --Fails otherwise, should it not ?
inductive Var : (Γ : List Ty) → Ty → Type
  | var {Γ A} (h : Γ.Has A) : Var Γ A

@[expose]
def Ren {T} (Γ Δ : List T) := ∀ A, Γ.Has A → Δ.Has A

def Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head => .head
  | _,.tail h => .tail (R _ h)

def Var.wk (R : Ren Γ Δ) : Var Γ B → Var Δ B
  | var h => .var (R _ h)

def Var.subst (s : ∀ {A}, Γ.Has A → Var Δ A) : Var Γ A → Var Δ A
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

  mod_def NatExt.subst extends Var.subst where
    match_1 s with
      | .const a => .const a
      | .plus a b => .plus (NatExt.subst s a) (NatExt.subst s b)

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

  #check Term.wk

  def Term.subst_ext {Γ : List LamTy} (s : ∀ {B}, Γ.Has B → Term Δ B): ∀ {B}, (A::Γ).Has B → Term (A::Δ) B
    | _,.head => .var .head
    | _,.tail h => Term.wk (s h)

  -- mod_def Term.subst extends NatExt.subst where
    -- match_1 with
      -- | .lam f => sorry
      -- | .app a b => .app (a.subst s) (b.subst s)
