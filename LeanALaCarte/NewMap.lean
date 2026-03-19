import LeanALaCarte.Basic
import LeanALaCarte.Elab
import Lean.Parser.Command
open Lean Parser Elab Meta Command

syntax "map_fn" ident+ "⇒" term : modular_command
