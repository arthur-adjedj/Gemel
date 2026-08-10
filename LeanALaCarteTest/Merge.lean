import LeanALaCarte

inductive A where
  | a : A → A

def A.sizeOf : A → Nat
  | a x => x.sizeOf + 1

theorem A.sizeOf_eq : A.sizeOf = A.sizeOf := by
  funext x
  induction x <;> congr

def A.diag : A → A → Prop
  | .a x, .a y => x.diag y

modular testB
  mod inductive B extends A where
    | b : B

  mod def B.sizeOf extends A.sizeOf where
    matcher match_1 with
      | .b => 0

  mod def B.sizeOf_eq extends A.sizeOf_eq where
    finally
      rfl

  mod def B.diag extends A.diag where
    matcher match_1 with
      | .b, .b => True
      | .a _,.b => False
      | .b, .a _ => False
modular end testB

modular testC
  mod inductive C extends A where
    | c : C → C → C

  mod def C.sizeOf extends A.sizeOf where
    matcher match_1 with
      | .c x y => x.sizeOf + y.sizeOf + 1

  mod def C.sizeOf_eq extends A.sizeOf_eq where
    finally
      intros; congr

  mod def C.diag extends A.diag where
    matcher match_1 with
      | .c x₁ y₁, .c x₂ y₂ => x₁.diag x₂ ∧ y₁.diag y₂
      | .a _, .c .. => False
      | .c ..,.a _ => False
modular end testC

modular testD (imports := testB, testC)

  mod inductive D extends B,C where

  mod def D.sizeOf extends B.sizeOf, C.sizeOf

  mod def D.sizeOf_eq extends B.sizeOf_eq, C.sizeOf_eq

  mod def D.diag extends B.diag, C.diag where
    matcher match_2 with
      | _,_ => False
