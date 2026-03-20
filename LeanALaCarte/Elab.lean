import LeanALaCarte.Util
import Lean.Meta.Check
import Lean.Elab

open Lean Meta Elab Command Term

declare_syntax_cat modular_command

def ModularCommand := TSyntax `modular_command

-- TODO manage extensions that different universes than the original type.
-- This is important eg for cases where users extend a function with additional arguments that require new universes
/- A modular extension is a term with some loose bvars. The first `numArgs` bvars correspond to the instantiation of the original term's arguments, the others correspond to holes that need to be filled in by users. -/
structure ModularExtension where
  translation : Expr
  levelParams : List Name
  numArgs : Nat
  numHoles : Nat
deriving Inhabited

instance : ToString ModularExtension where
  toString map := toString map.translation

abbrev ModularMap := Std.HashMap Name ModularExtension

abbrev ModularM := StateT ModularMap MetaM
abbrev ModularElabM := StateT ModularMap CommandElabM

instance [MonadLiftT m n] : MonadLiftT (StateT ρ m) (StateT ρ n) where
  monadLift m ρ := m ρ

instance [Monad m] [MonadQuotation m] : MonadQuotation (StateT ρ m) where
  getRef p := do
    let ref ← getRef
    return (ref,p)
  withRef stx x p := withRef stx (x p)
  getCurrMacroScope p := do
    let scope ← getCurrMacroScope
    return (scope,p)
  getContext p := do
    let ctx ← MonadQuotation.getContext
    return (ctx,p)
  withFreshMacroScope x p := withFreshMacroScope (x p)

instance [Monad m] [MonadRecDepth  m] : MonadRecDepth  (StateT ρ m) where
  withRecDepth n x p := MonadRecDepth.withRecDepth n (x p)
  getRecDepth p := do
    let n ← MonadRecDepth.getRecDepth
    return (n,p)
  getMaxRecDepth p := do
    let n ← MonadRecDepth.getMaxRecDepth
    return (n,p)

def ModularElab := Syntax → ModularElabM Unit

unsafe initialize modularElabAttribute : KeyedDeclsAttribute ModularElab ←
  mkElabAttribute ModularElab .anonymous `modular_elab Name.anonymous ``ModularElab "modular command"

private def elabModularCommandUsing (s : ModularMap) (stx : Syntax) : List (KeyedDeclsAttribute.AttributeEntry ModularElab) → ModularElabM Unit
  | []                => throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) =>
    catchInternalId unsupportedSyntaxExceptionId
      (do elabFn.value stx)
      (fun _ => do set s; elabModularCommandUsing s stx elabFns)

partial def elabModularCommand (stx : Syntax) : ModularElabM Unit :=
  try
    go
  finally
    addTraceAsMessages
where go := do
  withLogging <| withRef stx <| withIncRecDepth <| withFreshMacroScope do
    match stx with
    | Syntax.node _ k args =>
      if k == nullKind then
        args.forM elabModularCommand
      else withTraceNode `Modular.Elab (fun _ => return stx) (tag := stx.getKind.toString) do
        let s ← get
        let env ← getEnv
        let kNoScopes := k.eraseMacroScopes
        let elabFns :=
          let entries := modularElabAttribute.getEntries env k
          if entries.isEmpty && kNoScopes != k then
            modularElabAttribute.getEntries env kNoScopes
          else
            entries
        match elabFns with
        | []      =>
          elabCommand stx
            throwError "elaboration function for `{k}` has not been implemented"
        | elabFns =>
          elabModularCommandUsing s stx elabFns
    | _ => throwError "unexpected command"

def elabModularCommands (stxs : Array (TSyntax `modular_command)): ModularElabM Unit :=
  stxs.forM elabModularCommand


syntax "modular" manyIndent(modular_command) : command
elab_rules : command
| `(command| modular $[$m]* ) => do
  let _ ← elabModularCommands m |>.run {}

initialize
  registerTraceClass `Modular.Elab
  registerTraceClass `Modular.Subst
