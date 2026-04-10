module

public import LeanALaCarte.ModMap
public import LeanALaCarte.CheckTranslation
public import LeanALaCarte.ExtendInd
public import LeanALaCarte.ModularCommand
public import LeanALaCarte.ModDef

public section



inductive NatTy where
  | nat

inductive NatExt : (Γ : List NatTy) → NatTy → Type where
  | var {Γ A} (h : Γ.Mem A) : NatExt Γ A
  | const : Nat → NatExt Γ .nat
  | plus : NatExt Γ .nat → NatExt Γ .nat → NatExt Γ .nat

def NatExt.wk  : NatExt Γ B → NatExt Δ B
    | var h => .var sorry
    | .const a => .const a
    | .plus a b => .plus (NatExt.wk a) (NatExt.wk b)


-- /!\ This is a Lean Core error, not my fault, TODO file or fix yourself
/--
error: Failed to realize constant NatExt.wk.eq_1:
  failed to generate equational theorem for `NatExt.wk`
    failed to generate equality theorems for `match` expression `_private.LeanALaCarte.Test.STLCNoMod.0.NatExt.wk.match_1`
    Γ✝ : List NatTy
    B✝ : NatTy
    motive✝ : NatExt Γ✝ B✝ → Sort u_1
    a✝ : Nat
    h_1✝ : (h : List.Mem B✝ Γ✝) → motive✝ (NatExt.var h)
    h_2✝ : (a : Nat) → motive✝ (NatExt.const a)
    h_3✝ : (a b : NatExt Γ✝ NatTy.nat) → motive✝ (a.plus b)
    ⊢ (⋯ ▸ fun x motive h_1 h_2 h_3 h => ⋯ ▸ h_2 a✝) (NatExt.const a✝) motive✝ h_1✝ h_2✝ h_3✝ ⋯ = h_2✝ a✝
---
error: Unknown constant `NatExt.wk.eq_1`
-/
#guard_msgs in
#print equations NatExt.wk.eq_1
