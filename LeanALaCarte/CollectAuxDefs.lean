module

public import Lean.Meta.Basic

public section
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

partial def collectAuxDefs (cname : Name) (root : Name := cname): StateRefT S MetaM Unit := do
  -- modify fun map => if map.contains cname then map else map.insert cname {}
  let cinfo ← getConstInfo cname
  let names := cinfo.getUsedConstantsAsSet
  trace[Modular.Elab] "collectAuxDefs {cname} (root: {root}): {names.toArray}"
  for name in names do
    -- matchers get abstracted away, so we shouldn't add them as functions to be translated
    unless name.isAuxDeclOf root && !name.isMatcher do
      continue
    -- unless name.isMatcher do
    modify fun map =>
      if map.contains name then
        map.modify name (·.insert cname)
      else
        map.insert name (NameSet.insert {} cname)
    collectAuxDefs name root

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
  let (_,s) ← collectAuxDefs n |>.run {}
  return topoAuxDefs s

partial def Lean.Expr.collectAuxDefs (cname : Name) (e : Expr) (root : Name := cname) : StateRefT S MetaM Unit := do
  let names := e.foldConsts (init := {}) (flip NameSet.insert)
  trace[Modular.Elab] "Expr.collectAuxDefs {e} (root: {root}): {names.toArray}"
  for name in names do
    -- matchers get abstracted away, so we shouldn't add them as functions to be translated
    unless name.isAuxDeclOf root && !name.isMatcher do
      continue
    modify fun map =>
      if map.contains name then
        map.modify name (·.insert cname)
      else
        map.insert name (NameSet.insert {} cname)
    _root_.collectAuxDefs name root

@[deprecated "TODO do NOT rely on this function in the future. Since we use `.eq_def`s to elaborate functions now, there can indeed cycles in the declarations (e.g with mutual definitions), and this does not handle such cycles." (since := "recently") ]
def Lean.Expr.auxDefs (n : Name) (e : Expr) : MetaM (List Name) := do
  let (_,s) ← collectAuxDefs n e |>.run {}
  return topoAuxDefs s
