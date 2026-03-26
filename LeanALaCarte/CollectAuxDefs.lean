import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Lean.Meta.Basic
/-! Collect all auxiliary definitions of a given definition, return them in a topological sort.-/

open Lean Meta

abbrev S := Std.HashMap Name NameSet

partial def collectAuxDefs (root cname : Name) : StateRefT S MetaM Unit := do
  -- modify fun map => if map.contains cname then map else map.insert cname {}
  let cinfo ← getConstInfo cname
  let names := cinfo.getUsedConstantsAsSet
  names.forM fun name => do
    if name.isInternalDetail && root.isPrefixOf name then
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

def auxDefs (n : Name) : MetaM (List Name) := do
  let (_,s) ← collectAuxDefs n n |>.run {}
  return topoAuxDefs s
