import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Lean.Meta.Basic
import Lean.Elab
/-! Collect all auxiliary definitions of a given definition, return them in a topological sort.-/

open Lean Meta Elab

abbrev S := Std.HashMap Name NameSet

def Lean.Name.isAuxDeclOf (name root : Name) : Bool :=
  name.isInternalDetail && root.isPrefixOf name

def Lean.Name.isMatcher : Name → Bool
  | .str _ s   => matchPrefix s "match_"
  | _ => false
where
  /-- Check that a string begins with the given prefix, and then is only digits/'_'. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all fun c => c.isDigit || c == '_')

partial def collectAuxDefs (root cname : Name) : StateRefT S MetaM Unit := do
  -- modify fun map => if map.contains cname then map else map.insert cname {}
  let cinfo ← getConstInfo cname
  let names := cinfo.getUsedConstantsAsSet
  for name in names do
    unless name.isAuxDeclOf root do
      continue
    modify fun map =>
      if map.contains name then
        map.modify name (·.insert cname)
      else
        map.insert name (NameSet.insert {} cname)
    collectAuxDefs root name

partial def topoAuxDefs (map : S) : List Name :=
  let set := NameSet.ofList map.keys
  let (_,_,s) := go |>.run (set,[])
  s
where
  go : StateM (NameSet × List Name) Unit := do
    let (set,_) ← get
    unless set.isEmpty do
      let n := set.atIdx! 0
      visit n
      go
  visit (n : Name) : StateM (NameSet × List Name) Unit := do
    for depsOnName in map[n]! do
      let (set,_) ← get
      if set.contains depsOnName then
        visit depsOnName
    modify fun (set,res) => (set.erase n, n::res)

def auxDefs (n : Name) (root := n) : MetaM (List Name) := do
  let (_,s) ← collectAuxDefs root n |>.run {}
  return topoAuxDefs s
