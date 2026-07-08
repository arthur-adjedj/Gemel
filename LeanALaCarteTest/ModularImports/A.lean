import LeanALaCarte

set_option trace.Modular.Elab true
/--
trace: [Modular.Elab] []
---
trace: [Modular.Elab] ✅️ run_cmd
        return
-/
#guard_msgs in
modular (name := `A1)
  -- empty command
  run_cmd return

namespace A

/--
trace: [Modular.Elab] [_modular.A1]
---
trace: [Modular.Elab] ✅️ run_cmd
        return
-/
#guard_msgs in
modular (name := `A2) (imports := #[`A1])
  -- empty command
  run_cmd return

end A
