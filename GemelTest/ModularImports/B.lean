import GemelTest.ModularImports.A

set_option trace.Gemel.Elab true

/-- trace: [Gemel.Elab] (name := B) (imports := #[A1, A.A2]) -/
#guard_msgs in
modular B (imports := A1, A.A2)
