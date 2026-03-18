import LeanALaCarte.Util
import Lean.Meta.Check
import Qq
open Qq
open Lean Meta Elab Command Term

-- TODO manage extensions that different universes than the original type.
-- This is important eg for cases where users extend a function with additional arguments that require new universes
structure ModularExtension where
  translation : Expr
  levelParams : List Name
  numArgs : Nat
  numHoles : Nat
deriving Inhabited

abbrev ModularMap := Std.HashMap Name ModularExtension

abbrev ModularM := ReaderT ModularMap MetaM

partial def modmap (e : Expr) : ModularM Expr := do
  withTraceNode `Modular (λ exn => return m!"{exceptEmoji exn} modmap {e} ⇒ {exn.toOption}") do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const fnName lvls := fn then -- TODO manage universes better
    -- One might want to, if a constant is not already extended at this points but should be (e.g if its type contains things that have a partial map), delta-reduce the constant and map it as well.
    -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constant topographically to manage this.
    if let some ext := (← read)[fnName]? then
      unless ext.numArgs == args.size do
        return (← modmap (← Meta.etaExpand e))
      let res := ext.translation
        |>.instantiateLevelParams ext.levelParams lvls
        |>.instantiate (← args.mapM modmap)
      trace[Modular] m!"args instantiated : {res}"
      trace[Modular] m!"numHoles : {ext.numHoles}"
      let mvars ← Array.mkM ext.numHoles (mkFreshExprMVar none .synthetic)
      trace[Modular] m!"mvars : {mvars}"
      let res := res.instantiate mvars
      trace[Modular] m!"mvars instantiated : {res}"
      check res --gives a type to each synthetic mvar introduced, and throws a type-error if the generated term is ill-formed.
      return res
    else return mkAppN (← go fn) (← args.mapM modmap)
  else return mkAppN (← go fn) (← args.mapM modmap)
where
  go e : ModularM Expr := match e with
    | .sort _
    | .lit _ --What if you extend Nat ? you probably want literals to be translated accordingly, but that's an edge-case not worth thinking about for now
    | .bvar _ | .fvar _ | .mvar _ => pure e
    | .proj tyName idx struct => do
      if let some _ext := (← read)[tyName]? then
        /- Plan here:
           - look into the Expr, make sure its head is a constant that is structureLike (otherwise either throw an exception)
           - use the corresponding constant as the new head
           TODO what if the mapping is partial and the type contains holes ? In practice, shouldn't be an issue as said holes would morally be filled as part of the types of the mapped `struct`
        -/
        panic! "todo"
      else
        return .proj tyName idx (← modmap struct)
    | .letE ..
    | .lam .. =>
      lambdaLetTelescope e fun xs e => withModMappedLctx xs do
        mkLambdaFVars xs (← modmap e)
    | .forallE .. =>
      forallTelescope e fun xs e => withModMappedLctx xs do
        mkForallFVars xs (← modmap e)
    | .mdata _ e => modmap e
    | _ => unreachable!

  withModMappedLctx {α} (xs : Array Expr) (k : ModularM α) : ModularM α := do
    let localInsts ← Meta.getLocalInstances
    let mut lctx ← getLCtx
    for e in xs do
      let some lcdl := lctx.findFVar? e | unreachable!
      let ty ← Meta.withLCtx lctx localInsts (modmap lcdl.type)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setType ty)
      let some value := lcdl.value? | continue
      let value ← Meta.withLCtx lctx localInsts (modmap value)
      lctx := lctx.modifyLocalDecl e.fvarId! (·.setValue value)
    Meta.withLCtx lctx localInsts k

initialize
  registerTraceClass `Modular
