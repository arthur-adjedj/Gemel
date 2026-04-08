module

public import Lean.Meta.Basic
public import Lean.Util.ForEachExprWhere

public section

open Lean Meta

def Lean.Expr.collectDelayedAssignmentsWithArgs (e : Expr) : MetaM (Array Expr) := do
  let ref ← IO.mkRef #[]
  let cond e := e.getAppFn.isMVar
  e.forEachWhere (stopWhenVisited := true) cond fun e => do
    let fn := e.getAppFn
    let mvar := fn.mvarId!
    if let some assignment ← getDelayedMVarAssignment? mvar then
      trace[Meta.debug] "found delayed mvars: {e} => {Expr.mvar assignment.mvarIdPending} ({assignment.fvars})"
      let nargs := assignment.fvars.size
      let args := e.getAppArgs
      -- this is subobtimal. Ideally, the `forEachWhere` would simply visit until it encounters an app with just the right amount of args and use that term directly rather than reconstruct one using `mkAppRange`. However, `cond` cannot be effectful, so `getDelayedMVarAssignment?` cannot be used so easily. TODO extract the MCtx from the monad state and use that directly in the condition to get the DelaredMVars assignment non-monadically.
      ref.modify (·.push (mkAppRange fn 0 nargs args))

  ref.get
