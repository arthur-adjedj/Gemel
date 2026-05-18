module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Config
public section

open Lean Meta Elab Command Term

declare_syntax_cat modular_command

def ModularCommand := TSyntax `modular_command

-- TODO manage extensions that different universes than the original type.
-- This is important eg for cases where users extend a function with additional arguments that require new universes
/- A modular extension is a term with some loose bvars. The first `numArgs` bvars correspond to the instantiation of the original term's arguments, the others correspond to holes that need to be filled in by users. -/
structure ModularExtension where
  expr : Expr
  levelParams : List Name
  numArgs : Nat
  numHoles : Nat
deriving Inhabited

instance : ToMessageData ModularExtension where
  toMessageData m := m!"⦃ levelParams : {m.levelParams}\nnumArgs : {m.numArgs}\nnumHoles : {m.numHoles}\nexpr: {indentExpr m.expr}⦄"

instance : ToString ModularExtension where
  toString map := toString map.expr

abbrev ModularMap := Std.HashMap Name ModularExtension

structure MatchToExtend where
  matchName : Name
  mvar : MVarId
  originalMatch : Expr
  originalLCtx : LocalContext
  modMappedRhss : Array Expr

structure ModularElabState where
  map : ModularMap := {}

structure ModularState extends ModularElabState where
  matchesToExtend : Array MatchToExtend := #[]

class MonadModular (m) [Monad m] where
  getMap : m ModularMap
  modifyMap : (ModularMap → ModularMap) → m Unit
export MonadModular (getMap modifyMap)

class MonadModMappedLCtx (m) [Monad m] where
  getModMappedLCtx : m LocalContext
  withSetModMappedLCtx : LocalContext → m α → m α
export MonadModMappedLCtx (getModMappedLCtx withSetModMappedLCtx)

def addMapEntry [Monad m] [MonadModular m] (name : Name) (ext : ModularExtension) : m Unit :=
  modifyMap fun m => m.insert name ext

def addMapEntries [Monad m] [MonadModular m] (mappings : List (Name × ModularExtension)) : m Unit :=
  modifyMap fun m => m.insertMany mappings

def setMap [Monad m] [MonadModular m] (map: ModularMap) : m Unit := modifyMap fun _ => map

def withModifyMap [Monad m] [MonadModular m] (f : ModularMap → ModularMap) (k : m α) : m α := do
  let oldMap ← getMap
  modifyMap f
  let res ← k
  setMap oldMap
  return res

def withSetMap [Monad m] [MonadModular m] (map : ModularMap) (k : m α) : m α := do
  let oldMap ← getMap
  setMap map
  let res ← k
  setMap oldMap
  return res

def withModMappedLCtx [Monad m] [MonadModMappedLCtx m] [MonadControlT MetaM m] (k : m α) : m α := do
  let modMappedLCtx ← getModMappedLCtx
  withLCtx' modMappedLCtx do
    k

instance [Monad m] : MonadModular (StateT ModularState m) where
  getMap := get >>= pure ∘ (·.map)
  modifyMap f := modify fun m =>  {m with map := f m.map}

instance [Monad m] : MonadModular (StateT ModularElabState m) where
  getMap := get >>= pure ∘ (·.map)
  modifyMap f := modify fun m =>  {m with map := f m.map}

instance [Monad m] [MonadModular m] : MonadModular (ReaderT ρ m) where
  getMap _ := getMap
  modifyMap f _ := modifyMap f

instance [Monad m] : MonadModMappedLCtx (ReaderT LocalContext m) where
  getModMappedLCtx := read
  withSetModMappedLCtx lctx := withReader (fun _ => lctx)

class MonadMatchExt (m) [Monad m] where
  addMatchExtension : MatchToExtend → m Unit
  getMatchExtensions : m (Array MatchToExtend)
export MonadMatchExt (addMatchExtension getMatchExtensions)

instance [Monad m] : MonadMatchExt (StateT ModularState m) where
  addMatchExtension ext := modify fun m => {m with matchesToExtend := m.matchesToExtend.push ext}
  getMatchExtensions := get >>= pure ∘ ModularState.matchesToExtend

instance [Monad m] [MonadMatchExt m] : MonadMatchExt (ReaderT ρ m) where
  addMatchExtension ext _ := addMatchExtension ext
  getMatchExtensions _ := getMatchExtensions

abbrev ModularM := ReaderT LocalContext $ StateT ModularState TermElabM
abbrev ModularElabM := ReaderT LocalContext $ StateT ModularElabState CommandElabM

/- Warning: the function drops any potential match extension information. If you want to use this information later, use `withLiftModularM` -/
def liftModularM (k : ModularM α) : ModularElabM α := fun lctx map => do
  let (res,state) ← liftTermElabM (k lctx ⟨map,#[]⟩)
  return (res,state.toModularElabState)

def withLiftModularM (k : ModularM Unit) (k' : Array MatchToExtend → ModularElabM α) : ModularElabM α := fun lctx map => do
  let (_,state) ← liftTermElabM (k lctx ⟨map,#[]⟩)
  k' state.matchesToExtend |>.run lctx state.toModularElabState

public meta section

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


@[expose] def ModularElab := Syntax → ModularElabM Unit

unsafe initialize modularElabAttribute : KeyedDeclsAttribute ModularElab ←
  mkElabAttribute ModularElab .anonymous `modular_elab Name.anonymous ``ModularElab "modular command"

/--
Disables incremental command reuse *and* reporting for `act` if `cond` is true by setting
`Context.snap?` to `none`.
-/
def withoutModularCommandIncrementality (cond : Bool) (act : ModularElabM α) : ModularElabM α := do
  let opts ← getOptions
  -- Cancel old elaboration when discarding it (for commands without incrementality support)
  if cond then
    if let some old := (← readThe Command.Context).snap?.bind (·.old?) then
      old.val.cancelRec
  withTheReader Command.Context (fun ctx => { ctx with snap? := ctx.snap?.filter fun snap => Id.run do
    if let some old := snap.old? then
      if cond && opts.getBool `trace.Elab.reuse then
        dbg_trace "reuse stopped: guard failed at {old.stx}"
    return !cond
  }) act

def elabModularCommandUsing (s : ModularElabState) (stx : Syntax) : List (KeyedDeclsAttribute.AttributeEntry ModularElab) → ModularElabM Unit
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

mutual
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

  partial def elabChoiceAux (args : Array Syntax) (i : Nat) : ModularElabM Unit := do
    if h : i < args.size then
      catchInternalId unsupportedSyntaxExceptionId
        (elabModularCommand args[i])
        (fun _ => elabChoiceAux args (i + 1))
    else
      throwUnsupportedSyntax
end

def elabModularCommands (stxs : Array (TSyntax `modular_command)): ModularElabM Unit :=
  stxs.forM elabModularCommand

open Language in
/-- Snapshot for incremental processing of `modular` blocks. -/
structure ModularBlockSnapshot extends Snapshot where
  /-- Input modular commands. -/
  cmds : Array Syntax
  /-- Command state and modular map after each corresponding modular command. -/
  outputs : Array (Command.State × ModularElabState)
deriving TypeName

open Language in
instance : ToSnapshotTree ModularBlockSnapshot where
  toSnapshotTree s :=
    let children := s.outputs.foldl (init := #[]) fun children (st, _) =>
      children ++ st.snapshotTasks
    SnapshotTree.mk s.toSnapshot children

open Language in
/-- Live snapshot used while a modular block is still elaborating. -/
structure ModularBlockProgressSnapshot extends Snapshot where
  /-- The live body task for the modular block. -/
  body : SnapshotTask SnapshotTree
  /-- The eventual finalized modular block snapshot. -/
  result : SnapshotTask ModularBlockSnapshot
deriving TypeName

open Language in
instance : ToSnapshotTree ModularBlockProgressSnapshot where
  toSnapshotTree s :=
    SnapshotTree.mk s.toSnapshot #[s.body, s.result.map (sync := true) toSnapshotTree]
structure ModularSetup where
  name : Name := .anonymous
  imports : Array Name := #[]

declare_command_config_elab elabModularSetup ModularSetup

syntax (name := modular_block) "modular" Parser.Tactic.optConfig manyIndent(modular_command) : command

initialize modularMaps : IO.Ref (Std.HashMap Name ModularElabState) ← IO.mkRef {}

@[command_elab modular_block, incremental]
def elabModularBlock : CommandElab := fun stx => do
  match stx with
  | `(command| modular $cfg:optConfig $[$m]* ) => do
    let cfg ← elabModularSetup cfg
    let opts ← getOptions
    if let some snap := (← read).snap? then
      let oldSnap? : Option ModularBlockSnapshot := do
        let some old := snap.old? | none
        let some oldProgress := old.val.get.toTyped? ModularBlockProgressSnapshot | none
        pure oldProgress.result.task.get
      let mut map : ModularElabState := {}
      for name in cfg.imports do
        let some modmap := (← modularMaps.get)[name]?
          | throwError "Failed to import modular mapping {name}."
        map := ⟨map.map ∪ modmap.map⟩
      let oldCmds? := oldSnap?.map (·.cmds)
      let oldOutputs? := oldSnap?.map (·.outputs)
      let mut reusedPrefix := true
      let outputsRef ← IO.mkRef (Array.empty : Array (Command.State × ModularElabState))
      let mapRef ← IO.mkRef map
      let stateRef ← IO.mkRef (← get)
      let runNestedCommand (cmd : Syntax) (curMap : ModularElabState) : CommandElabM (Command.State × ModularElabState) := do
        if cmd.getKind.toString == "modular_run_command" then
          if let some old := (← read).snap?.bind (·.old?) then
            old.val.cancelRec
          withTheReader Command.Context (fun ctx => { ctx with snap? := none }) do
            elabCommand cmd[0]
            let state := (← get)
            return (state, curMap)
        else
          let (_, newMap) ← elabModularCommand cmd |>.run {} |>.run curMap
          let state := (← get)
          return (state, newMap)

      let mut commandTasks : Array (Language.SnapshotTask Language.SnapshotTree) := #[]
      for i in [:m.size] do
        let cmd : Syntax := m[i]!
        let prevTask? := commandTasks.back?
        let taskStx := cmd
        let reportingRange : Language.SnapshotTask.ReportingRange :=
          Language.SnapshotTask.defaultReportingRange (some taskStx)
        let commandTask ←
          if reusedPrefix then
            match oldCmds?, oldOutputs?, oldCmds?.bind (·[i]?), oldOutputs?.bind (·[i]?) with
            | some oldCmds, some oldOutputs, some oldCmd, some oldOutput =>
              if oldCmd.eqWithInfoAndTraceReuse opts cmd then
                let (oldState, oldMap) := oldOutput
                set oldState
                let outputs ← outputsRef.get
                outputsRef.set (outputs.push oldOutput)
                mapRef.set oldMap
                stateRef.set oldState
                let oldTree : Language.SnapshotTree := {
                  element := { diagnostics := .empty }
                  children := oldState.snapshotTasks
                }
                pure {
                  stx? := some taskStx
                  reportingRange := reportingRange
                  cancelTk? := none
                  task := .pure oldTree
                }
              else
                reusedPrefix := false
                let cancelTk ← IO.CancelToken.new
                let commandBody ←
                  Command.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
                    if let some prevTask := prevTask? then
                      let prevTree := prevTask.task.get
                      let prevWait ← prevTree.waitAll
                      let _ := prevWait.get
                    let prevState : Command.State := ← stateRef.get
                    set prevState
                    let curMap : ModularElabState := ← mapRef.get
                    let (state, newMap) ← runNestedCommand cmd curMap
                    set state
                    let outputs ← outputsRef.get
                    outputsRef.set (outputs.push (state, newMap))
                    mapRef.set newMap
                    stateRef.set state
                pure {
                  stx? := some taskStx
                  reportingRange := reportingRange
                  cancelTk? := some cancelTk
                  task := (← BaseIO.asTask (commandBody ()))
                }
            | _, _, _, _ =>
              reusedPrefix := false
              let cancelTk ← IO.CancelToken.new
              let commandBody ←
                Command.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
                  if let some prevTask := prevTask? then
                    let prevTree := prevTask.task.get
                    let prevWait ← prevTree.waitAll
                    let _ := prevWait.get
                  let prevState : Command.State := ← stateRef.get
                  set prevState
                  let curMap : ModularElabState := ← mapRef.get
                  let (state, newMap) ← runNestedCommand cmd curMap
                  set state
                  let outputs ← outputsRef.get
                  outputsRef.set (outputs.push (state, newMap))
                  mapRef.set newMap
                  stateRef.set state
              pure {
                stx? := some taskStx
                reportingRange := reportingRange
                cancelTk? := some cancelTk
                task := (← BaseIO.asTask (commandBody ()))
              }
          else
            let cancelTk ← IO.CancelToken.new
            let commandBody ←
              Command.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
                if let some prevTask := prevTask? then
                  let prevTree := prevTask.task.get
                  let prevWait ← prevTree.waitAll
                  let _ := prevWait.get
                let prevState : Command.State := ← stateRef.get
                set prevState
                let curMap : ModularElabState := ← mapRef.get
                let (state, newMap) ← runNestedCommand cmd curMap
                set state
                let outputs ← outputsRef.get
                outputsRef.set (outputs.push (state, newMap))
                mapRef.set newMap
                stateRef.set state
            pure {
              stx? := some taskStx
              reportingRange := reportingRange
              cancelTk? := some cancelTk
              task := (← BaseIO.asTask (commandBody ()))
            }
        commandTasks := commandTasks.push commandTask
      let bodyTree : Language.SnapshotTree := {
        element := { diagnostics := .empty }
        children := commandTasks
      }
      let bodyTask : Language.SnapshotTask Language.SnapshotTree :=
        .finished (some stx) bodyTree
      let resultTask : Language.SnapshotTask ModularBlockSnapshot := {
        stx? := some stx
        reportingRange := .skip
        cancelTk? := none
        task := (← BaseIO.asTask do
          let bodyTree := bodyTask.task.get
          let waitAllTask ← bodyTree.waitAll
          let _ := waitAllTask.get
          let outputs ← outputsRef.get
          let curMap  ← mapRef.get
          let messageLog := outputs.foldl (init := .empty) fun msgs (st, _) =>
            msgs ++ st.messages
          let diagnostics ← Language.Snapshot.Diagnostics.ofMessageLog messageLog
          let finalSnapshot : ModularBlockSnapshot := {
            diagnostics := diagnostics
            cmds := m.map (·.raw)
            outputs
          }
          return finalSnapshot)
      }
      snap.new.resolve <| .ofTyped {
        diagnostics := .empty
        body := bodyTask
        result := resultTask
        : ModularBlockProgressSnapshot
      }
      let _ := resultTask.task.get
      set (← stateRef.get)
      if !cfg.name.isAnonymous then
        let curMap : ModularElabState := ← mapRef.get
        modularMaps.modify (Std.HashMap.insert · cfg.name curMap)
    else
      let mut map : ModularElabState := {}
      for name in cfg.imports do
        let some modmap := (← modularMaps.get)[name]?
          | throwError "Failed to import modular mapping {name}."
        map := ⟨map.map ∪ modmap.map⟩
      let (_,endMap) ← elabModularCommands m |>.run {} |>.run map
      if !cfg.name.isAnonymous then
        modularMaps.modify (Std.HashMap.insert · cfg.name endMap)
  | _ => throwUnsupportedSyntax

initialize
  registerTraceClass `Modular.Elab
  registerTraceClass `Modular.Subst
  registerTraceClass `Modular.Match

end
