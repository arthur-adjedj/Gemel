import LeanALaCarte

set_option trace.Modular.Elab true
/-- trace: [Modular.Elab] [] -/
#guard_msgs in
modular (name := `A1)
  -- empty command
  run_cmd return

namespace A

/-- trace: [Modular.Elab] [A1] -/
#guard_msgs in
modular (name := `A2) (imports := #[`A1])
  -- empty command
  run_cmd return

end A
