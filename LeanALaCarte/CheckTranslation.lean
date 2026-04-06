import LeanALaCarte.ModMap

open Lean Elab Command Term

syntax (name := modular_check_translation) "#check_translation" ppLine term : modular_command

@[modular_elab modular_check_translation, incremental]
def elabModularCheckTranslation : ModularElab := fun stx => do
  match stx with
  | `(modular_command| #check_translation $e:term) => do
    let map ← getMap
    liftTermElabM do
      let e ← elabTerm e none
      let mappedTerm ← modMap map e
      logInfo m!"{mappedTerm}"
  | _ => throwUnsupportedSyntax
