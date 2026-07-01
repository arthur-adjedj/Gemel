import LeanALaCarteTest.ModularImports.A

set_option trace.Modular.Elab true

/-- trace: [Modular.Elab] [] -/
#guard_msgs in
modular (name := `B) (imports := #[`A1, `A.A2])
