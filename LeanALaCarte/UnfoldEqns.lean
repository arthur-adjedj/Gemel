import Lean.Meta.Eqns
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Meta.RecExt

open Lean Meta Elab

structure NonRec.EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr

inductive EqnInfo where
  | «nonrec» (info : NonRec.EqnInfo)
  | structural (info : Structural.EqnInfo)
  | wf (info : WF.EqnInfo)

namespace EqnInfo
def declName : EqnInfo → Name
  | «nonrec» {declName,..}
  | structural {declName,..}
  | wf {declName,..} => declName

def levelParams : EqnInfo → List Name
  | «nonrec» {levelParams,..}
  | structural {levelParams,..}
  | wf {levelParams,..} => levelParams

def type : EqnInfo → Expr
  | «nonrec» {type,..}
  | structural {type,..}
  | wf {type,..} => type

def value : EqnInfo → Expr
  | «nonrec» {value,..}
  | structural {value,..}
  | wf {value,..} => value

end EqnInfo

def getEqnInfo (n : Name) : MetaM EqnInfo := do
  if ← isRecursiveDefinition n then
    if let some info := Structural.eqnInfoExt.find? (← getEnv) n then
      return .structural info
    else if let some info := WF.eqnInfoExt.find? (← getEnv) n then
      return .wf info
    else
      throwError "Function {n} is recursive but not registered as either structural of well-founded"
  else
    let cinfo ← getConstInfo n
    let some value := cinfo.value? | throwError "Constant {n} does not have a value"
    return .nonrec { declName := n
                     levelParams := cinfo.levelParams
                     type := cinfo.type
                     value := value }
