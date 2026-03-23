import Lean

open Lean Meta

def Lean.Expr.collectDelayedAssignmentsWithArgs (e : Expr) : MetaM (Array Expr) := do
  let ref ← IO.mkRef #[]
  let cond e := e.getAppFn.isMVar
  e.forEachWhere (stopWhenVisited := true) cond fun e => ref.modify (·.push e)
  ref.get
