import Gemel

set_option trace.Modular.Elab true
/-- trace: [Modular.Elab] (name := A1) (imports := #[]) -/
#guard_msgs in
modular A1
  -- empty command
  -- run_cmd return
modular end A1
namespace A

/-- trace: [Modular.Elab] (name := A.A2) (imports := #[A1]) -/
#guard_msgs in
modular A2 (imports := A1)
  -- empty command
  run_cmd return
modular end A2

end A
