module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Config
import Lean.Elab.Tactic.Config
public section

open Lean Meta Elab Command Term

namespace IndExtension

/-- Encodes the extension of some inductive by some other inductive types. We constrain such extensions such that they are only allowed on types with the same number of universes, and same parameters/indices. Adding/Removing parameters/indices should be done as part of a separate inductive extension ran before the addition of new constructors. -/
structure AddInd where
  /-We ideally want extensions to extend arbitrary inductives family instantiations , not just the base case, e.g consider cases like:`inductive Foo (A) extends Prod A A where ...`.
  (Instantiating type parameters of the extended types here makes sense to me, instantiating indices not so much.)
  In practice, the toy system currently implemented simply maps from constant names to Exprs, so it wouldn't work for such cases. Instead, the real implementation will have to rely on something to unify patterns, e.g using `DiscrTree`s-/
  indName : Name

/-- Encodes the extension of some inductive types by adding new constructors. We constrain such extensions such that they are only allowed on types with the same number of universes, and same parameters/indices. Adding/Removing parameters/indices should be done as part of a separate inductive extension ran before the addition of new constructors.  -/
structure AddCtors where
  lparams : List Name
  indType : Expr
  addedCtors : Array Constructor

inductive _root_.IndExtension where
  | addCtors : AddCtors → IndExtension
  | addInd : AddInd → IndExtension
  -- should composition be primitive to IndExtensions ?

end IndExtension

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
  indFunctors : NameMap IndExtension := {}

structure ModularState extends ModularElabState where
  matchesToExtend : Array MatchToExtend := #[]

class MonadModular (m) [Monad m] where
  getMap : m ModularMap
  modifyMap : (ModularMap → ModularMap) → m Unit
  getIndFunctors : m (NameMap IndExtension)
  modifyIndFunctors : (NameMap IndExtension → NameMap IndExtension) → m Unit
export MonadModular (getMap modifyMap getIndFunctors modifyIndFunctors)

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
  let oldSt ← getMap
  modifyMap f
  let res ← k
  setMap oldSt
  return res

def withSetMap [Monad m] [MonadModular m] (map : ModularMap) (k : m α) : m α := do
  let oldSt ← getMap
  setMap map
  let res ← k
  setMap oldSt
  return res

def withModMappedLCtx [Monad m] [MonadModMappedLCtx m] [MonadControlT MetaM m] (k : m α) : m α := do
  let modMappedLCtx ← getModMappedLCtx
  withLCtx' modMappedLCtx do
    k

instance [Monad m] : MonadModular (StateT ModularState m) where
  getMap := get >>= pure ∘ (·.map)
  modifyMap f := modify fun m =>  {m with map := f m.map}
  getIndFunctors := get >>= pure ∘ (·.indFunctors)
  modifyIndFunctors f := modify fun m =>  {m with indFunctors := f m.indFunctors}

instance [Monad m] : MonadModular (StateT ModularElabState m) where
  getMap := get >>= pure ∘ (·.map)
  modifyMap f := modify fun m =>  {m with map := f m.map}
  getIndFunctors := get >>= pure ∘ (·.indFunctors)
  modifyIndFunctors f := modify fun m =>  {m with indFunctors := f m.indFunctors}

instance [Monad m] [MonadModular m] : MonadModular (ReaderT ρ m) where
  getMap _ := getMap
  modifyMap f _ := modifyMap f
  getIndFunctors _ := getIndFunctors
  modifyIndFunctors f _ := modifyIndFunctors f

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
  toSnapshotTree s := SnapshotTree.mk s.toSnapshot #[]

structure ModularSetup where
  name : Name := .anonymous
  imports : Array Name := #[]

declare_command_config_elab elabModularSetup ModularSetup

syntax (name := modular_block) "modular" Parser.Tactic.optConfig manyIndent(modular_command) : command

initialize modStates : IO.Ref (Std.HashMap Name ModularElabState) ← IO.mkRef {}

@[command_elab modular_block, incremental]
def elabModularBlock : CommandElab := fun stx => do
  match stx with
  | `(command| modular $cfg:optConfig $[$m]* ) => do
    let cfg ← elabModularSetup cfg
    if let some snap := (← read).snap? then
      let oldSnap? := do
        let oldSnap ← snap.old?
        oldSnap.val.get.toTyped? ModularBlockSnapshot
      if snap.old?.isSome && oldSnap?.isNone then
        snap.old?.forM (·.val.cancelRec)
      let opts ← getOptions
      let mut st : ModularElabState := {}
      for name in cfg.imports do
        let some modst := (← modStates.get)[name]?
          | throwError "Failed to import modular mapping {name}."
        st := ⟨st.map ∪ modst.map, st.indFunctors.union modst.indFunctors⟩
      let mut outputs : Array (Command.State × ModularElabState) := #[]
      let oldCmds? := oldSnap?.map (·.cmds)
      let oldOutputs? := oldSnap?.map (·.outputs)
      let mut reusedPrefix := true
      for i in [:m.size] do
        let cmd : Syntax := m[i]!
        let oldCmd? := oldCmds?.bind (·[i]?)
        let oldOutput? := oldOutputs?.bind (·[i]?)
        if reusedPrefix && oldCmd?.any (·.eqWithInfoAndTraceReuse opts cmd) then
          match oldOutput? with
          | some (oldState, oldSt) =>
            set oldState
            st := oldSt
            outputs := outputs.push (oldState, oldSt)
          | none =>
            reusedPrefix := false
            let (_, newMap) ← elabModularCommand cmd |>.run {} |>.run st
            st := newMap
            outputs := outputs.push ((← get), st)
        else
          reusedPrefix := false
          let (_, newst) ← elabModularCommand cmd |>.run {} |>.run st
          st := newst
          outputs := outputs.push ((← get), st)
      snap.new.resolve <| .ofTyped {
        diagnostics := .empty
        cmds := m.map (·.raw)
        outputs
        : ModularBlockSnapshot
      }
      if !cfg.name.isAnonymous then
        modStates.modify (Std.HashMap.insert · cfg.name st)
    else
      let mut st : ModularElabState := {}
      for name in cfg.imports do
        let some modst := (← modStates.get)[name]?
          | throwError "Failed to import modular mapping {name}."
        st := ⟨st.map ∪ modst.map, st.indFunctors.union modst.indFunctors⟩
      let (_,endMap) ← elabModularCommands m |>.run {} |>.run st
      if !cfg.name.isAnonymous then
        modStates.modify (Std.HashMap.insert · cfg.name endMap)
  | _ => throwUnsupportedSyntax

initialize
  registerTraceClass `Modular (inherited := true)
  registerTraceClass `Modular.Elab (inherited := true)
  registerTraceClass `Modular.Subst (inherited := true)
  registerTraceClass `Modular.Match (inherited := true)

end
