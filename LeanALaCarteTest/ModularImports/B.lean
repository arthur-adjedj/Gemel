import LeanALaCarteTest.ModularImports.A

set_option trace.Modular.Elab true

/-- trace: [Modular.Elab] (name := B) (imports := #[A1, A.A2]) -/
#guard_msgs in
modular B (imports := A1, A.A2)
