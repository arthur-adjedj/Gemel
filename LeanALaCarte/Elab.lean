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

abbrev ModularM := StateT ModularMap TermElabM
abbrev ModularElabM := StateT ModularMap CommandElabM

def liftModularM (k : ModularM α) : ModularElabM α := fun map => liftTermElabM (k map)

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

/--
Disables incremental command reuse *and* reporting for `act` if `cond` is true by setting
`Context.snap?` to `none`.
-/
def withoutModularCommandIncrementality (cond : Bool) (act : ModularElabM α) : ModularElabM α := do
  let opts ← StateT.lift getOptions
  -- Cancel old elaboration when discarding it (for commands without incrementality support)
  if cond then
    if let some old := (← read).snap?.bind (·.old?) then
      StateT.lift <| old.val.cancelRec
  withReader (fun ctx => { ctx with snap? := ctx.snap?.filter fun snap => Id.run do
    if let some old := snap.old? then
      if cond && opts.getBool `trace.Elab.reuse then
        dbg_trace "reuse stopped: guard failed at {old.stx}"
    return !cond
  }) act

private def elabModularCommandUsing (s : ModularMap) (stx : Syntax) : List (KeyedDeclsAttribute.AttributeEntry ModularElab) → ModularElabM Unit
  | []                =>
    withInfoTreeContext
      (mkInfoTree := fun trees =>
        pure <| InfoTree.node (Info.ofCommandInfo { elaborator := `no_elab, stx := stx }) trees)
      (throwError "unexpected syntax{indentD stx}")
  | (elabFn::elabFns) =>
    catchInternalId unsupportedSyntaxExceptionId
      (do
        -- Prevent unsupported modular elaborators from accidentally accessing `Context.snap?`
        -- (e.g. via nested incrementality-enabled command elaboration).
        withoutModularCommandIncrementality (!(← isIncrementalElab elabFn.declName)) do
        withInfoTreeContext
          (mkInfoTree := fun trees =>
            pure <| InfoTree.node (Info.ofCommandInfo { elaborator := elabFn.declName, stx := stx }) trees)
          (elabFn.value stx))
      (fun _ => do set s; elabModularCommandUsing s stx elabFns)

partial def elabModularCommand (stx : Syntax) : ModularElabM Unit :=
  try
    go
  finally
    addTraceAsMessages
where go := do
  let rec elabChoiceAux (args : Array Syntax) (i : Nat) : ModularElabM Unit := do
    if h : i < args.size then
      catchInternalId unsupportedSyntaxExceptionId
        (elabModularCommand args[i])
        (fun _ => elabChoiceAux args (i + 1))
    else
      throwUnsupportedSyntax
  withLogging <| withRef stx <| withIncRecDepth <| withFreshMacroScope do
    match stx with
    | Syntax.node _ k args =>
      if k == nullKind then
        -- Like regular command elaboration, disable incrementality for quoted command lists.
        withoutModularCommandIncrementality true do
          args.forM elabModularCommand
      else if k.toString == "choice" then
        elabChoiceAux args 0
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

open Language in
/-- Snapshot for incremental processing of `modular` blocks. -/
structure ModularBlockSnapshot extends Snapshot where
  /-- Input modular commands. -/
  cmds : Array Syntax
  /-- Command state and modular map after each corresponding modular command. -/
  outputs : Array (Command.State × ModularMap)
deriving TypeName

open Language in
instance : ToSnapshotTree ModularBlockSnapshot where
  toSnapshotTree s := SnapshotTree.mk s.toSnapshot #[]


syntax (name := modular_block) "modular" manyIndent(modular_command) : command

@[command_elab modular_block, incremental]
def elabModularBlock : CommandElab := fun stx => do
  match stx with
  | `(command| modular $[$m]* ) => do
    if let some snap := (← read).snap? then
      let oldSnap? := do
        let oldSnap ← snap.old?
        oldSnap.val.get.toTyped? ModularBlockSnapshot
      if snap.old?.isSome && oldSnap?.isNone then
        snap.old?.forM (·.val.cancelRec)
      let opts ← getOptions
      let mut map : ModularMap := {}
      let mut outputs : Array (Command.State × ModularMap) := #[]
      let oldCmds? := oldSnap?.map (·.cmds)
      let oldOutputs? := oldSnap?.map (·.outputs)
      let mut reusedPrefix := true
      for i in [:m.size] do
        let cmd : Syntax := m[i]!
        let oldCmd? := oldCmds?.bind (·[i]?)
        let oldOutput? := oldOutputs?.bind (·[i]?)
        if reusedPrefix && oldCmd?.any (·.eqWithInfoAndTraceReuse opts cmd) then
          match oldOutput? with
          | some (oldState, oldMap) =>
            set oldState
            map := oldMap
            outputs := outputs.push (oldState, oldMap)
          | none =>
            reusedPrefix := false
            let (_, newMap) ← elabModularCommand cmd |>.run map
            map := newMap
            outputs := outputs.push ((← get), map)
        else
          reusedPrefix := false
          let (_, newMap) ← elabModularCommand cmd |>.run map
          map := newMap
          outputs := outputs.push ((← get), map)
      snap.new.resolve <| .ofTyped {
        diagnostics := .empty
        cmds := m.map (·.raw)
        outputs
        : ModularBlockSnapshot
      }
    else
      let _ ← elabModularCommands m |>.run {}
  | _ => throwUnsupportedSyntax

initialize
  registerTraceClass `Modular.Elab
  registerTraceClass `Modular.Subst
