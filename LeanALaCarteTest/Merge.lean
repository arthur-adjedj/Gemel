import LeanALaCarte

inductive A where
  | a : A → A

def A.sizeOf : A → Nat
  | a x => x.sizeOf + 1

modular (name := `B)
  inductive B extends A where
    | b : B

  mod def B.sizeOf extends A.sizeOf where
    matcher match_1 with
      | .b => 0

modular (name := `C)
  inductive C extends A where
    | c : C → C → C

  mod def C.sizeOf extends A.sizeOf where
    matcher match_1 with
      | .c x y => x.sizeOf + y.sizeOf + 1

set_option trace.Modular true
modular (imports := #[`B,`C])

  inductive D extends B,C where

  mod def D.sizeOf extends B.sizeOf, C.sizeOf
