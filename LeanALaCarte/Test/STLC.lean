import LeanALaCarte.ModMap
import LeanALaCarte.CheckTranslation
import LeanALaCarte.ExtendInd
import LeanALaCarte.ModularCommand
import LeanALaCarte.ModDef

--Utils for later
section
inductive List.Has : List α → α → Type where
  | head : List.Has (a::l) a
  | tail : List.Has l a → List.Has (b::l) a

abbrev Rel (α : Sort u) := α → α → Prop

inductive RTC (R : Rel α) : Rel α where
  | intro : R a b → RTC R a b
  | refl : RTC R a a
  | trans : R a b → RTC R b c → RTC R a c

def Confluent (R : Rel α) : Prop := ∀ (a b c : α), R a b → R a c → ∃ d, RTC R b d ∧ RTC R c d

end

inductive Ty where
  -- Needed to avoid issue `lean4#13364` (https://github.com/leanprover/lean4/issues/13364)
  | dummy

-- Not needed for the formalisation done here, but without it, the translation of recursors and other auxiliaries is currently fucked up..
set_option inductive.autoPromoteIndices false
inductive Var  : List Ty → Ty → Type
  | var (h : Γ.Has A) : Var Γ A

def Ren {T} (Γ Δ : List T) := ∀ A, Δ.Has A → Γ.Has A

def Ren.id : Ren Γ Γ := fun _ h => h

def Ren.comp (R₁ : Ren Γ₁ Γ₂) (R₂ : Ren Γ₂ Γ₃) : Ren Γ₁ Γ₃ := fun _ h => R₁ _ (R₂ _ h)

infixr:90 " ∘ᵣ " => Ren.comp

def Ren.ext (R : Ren Γ Δ) A: Ren (A::Γ) (A::Δ)
  | _,.head => .head
  | _,.tail h => .tail (R _ h)

theorem Ren.ext_comp_ext (R₁ : Ren Γ₁ Γ₂) (R₂ : Ren Γ₂ Γ₃) : (R₁.ext A) ∘ᵣ R₂.ext A = (R₁ ∘ᵣ R₂).ext A := by
  funext _ h
  cases h <;> rfl

def Ren.drop (A) (R : Ren Γ Δ): Ren (A::Γ) Δ := fun _ h => .tail (R _ h)

def Ren.wk (A) : Ren (A::Γ) Γ := Ren.drop _ .id

def Var.wk (R : Ren Γ Δ) : Var Δ B → Var Γ B
  | var h => .var (R _ h)

theorem Var.wk_comp (R₁ : Ren Γ₁ Γ₂) (R₂ : Ren Γ₂ Γ₃) : Var.wk R₁ (Var.wk R₂ t) = Var.wk (R₁ ∘ᵣ R₂) t := by
  induction t generalizing Γ₁ Γ₂
  rfl

def Var.Subst (Γ Δ : List Ty) := ∀ ⦃A⦄, Δ.Has A → Var Γ A

def Var.Subst.id : Var.Subst Γ Γ := fun _ h => .var h

def Var.subst (s : Var.Subst Γ Δ) : Var Δ A → Var Γ A
  | .var h => s h

def Var.Subst.comp (s₁ : Var.Subst Γ₁ Γ₂) (s₂ : Var.Subst Γ₂ Γ₃) : Var.Subst Γ₁ Γ₃ :=
  fun _ h => Var.subst s₁ (s₂ h)

theorem Var.subst_id : Var.subst Var.Subst.id t = t := by
  induction t
  rfl
theorem Var.wk_subst :
  ∀ {Ξ Δ Γ A} (R : Ren Γ Δ) (s : Var.Subst Δ Ξ) (t : Var Ξ A),
    Var.wk R (Var.subst (A := A) s t) = Var.subst (fun _ h => Var.wk R (s h)) t := by
  intro Ξ Δ Γ A R s t
  induction t generalizing Γ Δ; rfl --These generalisations are necessary for later proofs to be well-formed, any way induction proofs could be "generalized after the fact" ?

inductive Var.Step : Var Γ A → Var Γ A → Prop where

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

  mod_def NatExt.wk_comp extends Var.wk_comp where
    finally
      · intros
        simp only [NatExt.wk]
      · intro _ _ _ a_ih b_ih _ _ _ _
        simp [NatExt.wk,a_ih,b_ih]

  mod_def NatExt.Subst extends Var.Subst

  mod_def NatExt.subst extends Var.subst where
    match_1 s with
      | .const a => .const a
      | .plus a b => .plus (NatExt.subst s a) (NatExt.subst s b)

  mod_def NatExt.Subst.id extends Var.Subst.id
  mod_def NatExt.Subst.comp extends Var.Subst.comp

  mod_def NatExt.subst_id extends Var.subst_id where
    finally
      · intros; rfl
      · intro Γ a b a_ih b_ih
        rw [NatExt.subst,a_ih,b_ih]

  mod_def NatExt.wk_subst extends Var.wk_subst where
    finally
      · intros
        rfl
      · intros Γ a b a_ih b_ih s
        simp [NatExt.subst,NatExt.wk,a_ih,b_ih]

  inductive NatExt.Step extends Var.Step where
    | plus_const : NatExt.Step (.plus (.const a) (.const b)) (.const (a + b))
    | plus_lhs : NatExt.Step a₁ a₂ → NatExt.Step (.plus a₁ b) (.plus a₂ b)
    | plus_rhs : NatExt.Step b₁ b₂ → NatExt.Step (.plus a b₁) (.plus a b₂)

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

  mod_def Term.wk_comp extends NatExt.wk_comp where
    finally
    · intro _ _ _ _ a_ih _ _ _ _
      simp only [Term.wk,a_ih,Ren.ext_comp_ext]
    · intros
      clear Term.wk_comp
      simp only [Term.wk, *]

  mod_def Term.Subst extends NatExt.Subst
  mod_def Term.Subst.id extends NatExt.Subst.id

  theorem Term.wk_id {Γ : List LamTy} {h : Γ.Has A} : Term.wk (Ren.wk B) (Subst.id A h) = (Subst.id A h.tail) := rfl

  def Term.subst_ext (s : Term.Subst Γ Δ) A : Term.Subst (A::Γ) (A::Δ)
    | _ ,.head => .var .head
    | _ ,.tail h => Term.wk (Ren.wk _) (s h)

  theorem Term.subst_ext_id : @Term.subst_ext Γ Γ Term.Subst.id A = Term.Subst.id := by
    funext _ h
    cases h
    · rfl
    · rw [subst_ext]
      rfl
  def Term.subst_wk (a : Term Γ A) : Term.Subst Γ (A::Γ)
    | _,.head => a
    | _,.tail h => .var h

  mod_def Term.subst extends NatExt.subst where
    match_1 with
      | _, .lam f => .lam (Term.subst (Term.subst_ext s _) f)
      | _, .app a b => .app (Term.subst s a) (Term.subst s b)

  mod_def Term.Subst.comp extends NatExt.Subst.comp

  infixr:90 " ∘ₛₜ " => Term.Subst.comp

  mod_def Term.subst_id extends NatExt.subst_id where
    finally
      · intro _ _ _ a a_ih
        rw [Term.subst, Term.subst_ext_id,a_ih]
      · intro _ _ _ a b a_ih b_ih
        rw [Term.subst,a_ih,b_ih]

  inductive Term.Step extends NatExt.Step where
    | beta : Term.Step (.app (.lam f) x) (Term.subst (Term.subst_wk x) f)
    | lam : Term.Step f₁ f₂ → Term.Step (.lam f₁) (.lam f₂)
    | app_lhs : Term.Step f₁ f₂ → Term.Step (.app f₁ x) (.app f₂ x)
    | app_rhs : Term.Step x₁ x₂ → Term.Step (.app f x₁) (.app f x₂)

  local infixr:75 " ⤳ " => Term.Step
  local infixr:75 " ⤳⋆ " => RTC Term.Step

  mod_def Term.wk_subst extends NatExt.wk_subst where
    finally
    · intro A Γ B f f_ih R s _ _
      simp [Term.subst,Term.wk,f_ih]
      congr
      funext x h
      cases h
      · rfl
      · simp only [Term.subst_ext,Term.wk_comp]
        rfl
    · intro A Γ B f x ihf ihx
      simp [Term.subst, Term.wk, ihf, ihx]

  theorem Term.subst_ext_comp {Γ₁ Γ₂ Γ₃} (s₁ : Term.Subst Γ₁ Γ₂) (s₂ : Term.Subst Γ₂ Γ₃)
    : Subst.comp (Term.subst_ext s₁ A) (Term.subst_ext s₂ A) = Term.subst_ext (s₁.comp s₂) A := by
      funext _ h
      cases h
      · rfl
      · simp [Subst.comp,subst_ext,wk_subst]
        sorry

  theorem Term.subst_comp {Γ Δ Ξ : List LamTy} :
    ∀ {A} (t : Term Ξ A), ∀ (s₁ : Subst Γ Δ) (s₂ : Subst Δ Ξ),
    subst s₁ (subst s₂ t) = subst (s₁.comp s₂) t := by
      intro A t
      induction t generalizing Γ Δ <;> intro s₁ s₂ <;> try rfl
      case plus _ a b a_ih b_ih =>
        simp [subst,a_ih,b_ih]
      case lam _ _ a a_ih =>
        rw [subst,subst,subst,a_ih,subst_ext_comp]
      case app _ _ _ a b a_ih b_ih =>
        simp [subst, a_ih,b_ih]


  theorem Term.Step.Confluent : Confluent (@Term.Step Γ A) := sorry
