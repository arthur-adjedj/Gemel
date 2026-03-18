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
    trace[Modular] "head is fn {fnName}"
    if let some ext := (← read)[fnName]? then
      trace[Modular] "found ext for {fnName}"
      unless ext.numArgs == args.size do
        return (← modmap (← Meta.etaExpand e))
      trace[Modular] "No eta expansion needed yay"
      let res := ext.translation
        |>.instantiateLevelParams ext.levelParams lvls
        |>.instantiate (← args.mapM modmap)
      trace[Modular] m!"args instantiated : {res}"
      trace[Modular] m!"numHoles : {ext.numHoles}"
      let mvars ← Array.mkM ext.numHoles (mkFreshExprMVar none .synthetic)
      trace[Modular] m!"mvars : {mvars}"
      let res := res.instantiate mvars
      trace[Modular] m!"mvars instantiated : {res}"
      check res --should give a type to each synthetic mvar, and throw a type-error if the generated term is ill-formed.
      return res
    else return mkAppN (← go fn) (← args.mapM modmap)
  else return mkAppN (← go fn) (← args.mapM modmap)
where
  go e : ModularM Expr := match e with
    | .sort _ | .lit _ --What if you extend Nat ? you probably want literals to be translated accordingly, but that's an edge-case
    | .bvar _ | .fvar _ | .mvar _ => pure e
    | .proj .. => panic! "todo"
    | .letE ..
    | .lam .. =>
      lambdaLetTelescope e fun xs e => withModMappedLctx xs do
        trace[Modular] m!"modmapped fvars : {xs}"
        mkLambdaFVars xs (← modmap e)
    | .forallE .. =>
      forallTelescope e fun xs e => withModMappedLctx xs do
        trace[Modular] m!"modmapped fvars : {xs}"
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
