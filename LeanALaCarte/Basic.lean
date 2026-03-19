import LeanALaCarte.Util
import Lean.Meta.Check
import Qq
open Qq
open Lean Meta Elab Command Term

-- TODO manage extensions that different universes than the original type.
-- This is important eg for cases where users extend a function with additional arguments that require new universes
/- A modular extension is a term with some loose bvars. The first `numArgs` bvars correspond to the instantiation of the original term's arguments, the others correspond to holes that need to be filled in by users. -/
structure ModularExtension where
  translation : Expr
  levelParams : List Name
  numArgs : Nat
  numHoles : Nat
deriving Inhabited

abbrev ModularMap := Std.HashMap Name ModularExtension

abbrev ModularM := ReaderT ModularMap MetaM

partial def modmap (e : Expr) : ModularM Expr := do
  withIncRecDepth do
  withTraceNode `Modular (λ exn => return m!"{exceptEmoji exn} modmap {e} ⇒ {exn.toOption}") do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const fnName lvls := fn then -- TODO manage universes better
    -- One might want to, if a constant is not already extended at this point but should be (e.g if its type contains things that have a partial map), delta-reduce the constant and map it as well.
    -- This is not the right way to go and could lead to very expensive and deep recursions. Instead, this functions should be called with the assumption that all necessary functions have a corresponding mapping or don't need one. The core loop will simply sort constants topographically to ensure this.
    if let some ext := (← read)[fnName]? then
      --If the partial map has more args than given in the term, we need to eta-expand to avoid producing a term with loose bvars.
      -- TODO what if the term is overapplied ?
      unless ext.numArgs == args.size do
        return ← modmap (← Meta.etaExpand e)
      let newArgs ← args.mapM modmap
      let res := ext.translation
        |>.instantiateLevelParams ext.levelParams lvls
        |>.instantiate newArgs
      trace[Modular] m!"args instantiated : {res}"
      trace[Modular] m!"numHoles : {ext.numHoles}"
      -- The produced mvars are "synthetic", i.e they ought to be resolved by the users using tactics or other automations rather than through unification. We may want to use some heuristics in some cases to resolve these automatically when possible.
      let mvars ← Array.mkM ext.numHoles (mkFreshExprMVar none .synthetic)
      trace[Modular] m!"mvars : {mvars}"
      let res := res.instantiate mvars
      trace[Modular] m!"mvars instantiated : {res}"
      check res --typecheck the result, which should give a sensible type to each synthetic mvar introduced in the term, and throw a type-error if the generated term is ill-formed.
      return res
    else return mkAppN (← go fn) (← args.mapM modmap)
  else return mkAppN (← go fn) (← args.mapM modmap)
where
  go e : ModularM Expr := match e with
    | .sort _
    | .lit _ --What if you extend Nat/String ? you probably want literals to be translated accordingly, but that's an edge-case not worth thinking about for now
    | .bvar _ | .fvar _ | .mvar _ => pure e
    | .proj tyName idx struct => do
      if let some _ext := (← read)[tyName]? then
        /- Plan here:
           - look into `ext.translation`, make sure its head is a constant that is structureLike (otherwise throw an exception, we cannot produce "projections" for a type that has more than one constructor/is indexed)
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
