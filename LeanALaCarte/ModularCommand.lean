module

public meta import LeanALaCarte.Elab
public meta import Lean.Elab.GuardMsgs
public import LeanALaCarte.Elab

public meta section

open Lean Elab Command
open Lean.Elab.Tactic.GuardMsgs

def messageToString (msg : Message) (reportPos? : Option Nat) : CommandElabM String := do
  let mut str ← liftIO <| msg.data.toString
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  if !("\n".isPrefixOf str) then
    str := " " ++ str
  if msg.isTrace then
    str := "trace:" ++ str
  else
    match msg.severity with
    | MessageSeverity.information => str := "info:" ++ str
    | MessageSeverity.warning => str := "warning:" ++ str
    | MessageSeverity.error => str := "error:" ++ str
  if let some line := reportPos? then
    let showRelPos (line : Nat) (pos : Position) := s!"+{pos.line - line}:{pos.column}"
    let showEndPos := msg.endPos.elim "*" fun endPos =>
      if endPos.line = msg.pos.line then s!"{endPos.column}" else showRelPos line endPos
    str := s!"@ {showRelPos line msg.pos}...{showEndPos}\n" ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

def runAndCollectModularMessages (cmd : TSyntax `modular_command) : ModularElabM MessageLog := do
  let oldState ← StateT.lift get
  StateT.lift <| modify fun st => { st with messages := .empty, snapshotTasks := #[] }
  withReader ({ · with snap? := none }) do
    elabModularCommand cmd
  let newState ← StateT.lift get
  let msgs := newState.messages ++
    (newState.snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty)
  StateT.lift <| modify fun st => { st with messages := oldState.messages, snapshotTasks := oldState.snapshotTasks }
  return msgs

def withScopedOptions (opts : Options) (x : ModularElabM Unit) : ModularElabM Unit := do
  let oldOpts ← StateT.lift getOptions
  StateT.lift <| modifyScope fun scope => { scope with opts := opts }
  try
    x
  finally
    StateT.lift <| modifyScope fun scope => { scope with opts := oldOpts }

syntax (name := modular_guard_msgs)
  (docComment)? "#guard_msgs" (ppSpace guardMsgsSpec)? " in" ppLine modular_command : modular_command

@[modular_elab modular_guard_msgs]
def elabModularGuardMsgs : ModularElab := fun stx => do
  match stx with
  | `(modular_command| $[$dc?:docComment]? #guard_msgs%$tk $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (StateT.lift <| getDocStringText ·)).getD ""
      |>.trimAscii |>.copy |> removeTrailingWhitespaceMarker
    let { whitespace, ordering, filterFn, reportPositions, substring } ← StateT.lift <| parseGuardMsgsSpec spec?
    let msgs ← runAndCollectModularMessages cmd
    let mut toCheck : MessageLog := .empty
    let mut toPassthrough : MessageLog := .empty
    for msg in msgs.toList do
      if msg.isSilent then
        continue
      match filterFn msg with
      | .check => toCheck := toCheck.add msg
      | .drop => pure ()
      | .pass => toPassthrough := toPassthrough.add msg
    let map ← StateT.lift getFileMap
    let reportPos? :=
      if reportPositions then
        tk.getPos?.map (map.toPosition · |>.line)
      else
        none
    let strings ← toCheck.toList.mapM (fun msg => StateT.lift <| messageToString msg reportPos?)
    let res := "---\n".intercalate (ordering.apply strings) |>.trimAscii |>.copy
    let passed := if substring then
      (whitespace.apply res).contains (whitespace.apply expected)
    else
      whitespace.apply expected == whitespace.apply res
    if passed then
      StateT.lift <| modify fun st => { st with messages := st.messages ++ toPassthrough }
    else
      StateT.lift <| modify fun st => { st with messages := st.messages ++ msgs }
      let feedback :=
        if guard_msgs.diff.get (← StateT.lift getOptions) then
          let diff := Diff.diff (expected.split '\n').toStringArray (res.split '\n').toStringArray
          Diff.linesToString diff
        else
          res
      StateT.lift <| logErrorAt tk m!"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n{feedback}"
      StateT.lift <| pushInfoLeaf (.ofCustomInfo { stx := ← StateT.lift getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax

partial def findGuardMsgFailure (node : InfoTree) : Option (Syntax × String) :=
  match node with
  | .node i cs =>
    match i with
    | .ofCustomInfo { stx, value } =>
      match value.get? GuardMsgFailure with
      | some res => some (stx, res.res)
      | none => cs.findSome? findGuardMsgFailure
    | _ => cs.findSome? findGuardMsgFailure
  | _ => none

open Lean.CodeAction Lean.Server Lean.Server.RequestM in
@[command_code_action]
def modularGuardMsgsCodeAction : Lean.CodeAction.CommandCodeAction := fun _ _ _ node => do
  let res := findGuardMsgFailure node
  let some (stx, res) := res | return #[]
  let doc ← readDoc
  let eager := {
    title := "Update #guard_msgs with generated message"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let dc := stx[0]
      let some start := dc.getPos? false | return eager
      let some tail := dc.getTailPos? (canonicalOnly := true) | return eager
      let res := revealTrailingWhitespace res
      let newText := if res.isEmpty then
        ""
      else if res.length ≤ 100-7 && !res.contains '\n' then
        s!"/-- {res} -/"
      else
        s!"/--\n{res}\n-/"
      pure { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]

syntax (name := modular_set_option)
  "set_option " Lean.Parser.identWithPartialTrailingDot ppSpace optionValue " in" ppLine modular_command : modular_command

@[modular_elab modular_set_option]
def elabModularSetOption : ModularElab := fun stx => do
  match stx with
  | `(modular_command| set_option $id $val in $cmd) => do
    let opts ← elabSetOption id val
    withScopedOptions opts do
      elabModularCommand cmd
  | _ => throwUnsupportedSyntax

syntax (name := modular_run_command) command : modular_command

@[modular_elab modular_run_command, incremental]
def elabModularElabCommand : ModularElab := fun stx => do
  if stx.isOfKind ``modular_run_command then
    StateT.lift <| elabCommand stx[0]
  else
    throwUnsupportedSyntax

end
