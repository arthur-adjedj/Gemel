module

import LeanALaCarte.Elab
import Lean.Meta.Basic
open Lean Meta

def throwNotSameShape (e₁ e₂ : Expr) : CoreM α :=
  throwError "The following terms do not have the same shape, and thus cannot be merged: {indentExpr e₁} {indentExpr e₂}"

partial def mergeExprs (e₁ e₂ : Expr) : ModularM Expr :=
  match e₁, e₂ with
  -- Where the real magic happens
  | .mvar m, e | e, .mvar m => do
    let fallback _ := do
      -- If nothing interesting is happening between the mvars, we just return the first one.. ?
      -- TODO some better fallback is probably possible, eg if one of the mvars is a matcher and the other is not
      -- TODO maybe assign `m'` to `m` when possible ?
      return e
    let .mvar m' := e | fallback ()
    let exts ← getMatchExtensions
    let some _matchers₁ := exts.get? m | fallback ()
    let some _matchers₂ := exts.get? m' | fallback ()
    modifyMatchExtensions fun exts => exts --TODO erase `m'` from the map, merge matchers in `m` entry
    return e₁
  | .bvar _, .bvar _
  | .fvar _, .fvar _
  | .lit _, .lit _
  | .sort _, .sort _ => do
    unless e₁ == e₂ do --might be too strict ? what about let-bound or proof-irrelevant fvars ?
      throwNotSameShape e₁ e₂
    return e₁
  | .proj tyName₁ idx₁ struct₁, .proj tyName₂ idx₂ struct₂ => do
    unless tyName₁ == tyName₂ && idx₁ == idx₂ do
      throwNotSameShape e₁ e₂
    let e ← mergeExprs struct₁ struct₂
    return .proj tyName₁ idx₁ e
  | .letE n₁ t₁ bd₁ v₁ nonDep₁ , .letE _n₂ t₂ bd₂ v₂ nonDep₂ => do
    unless nonDep₁ == nonDep₂ do --too strict ? this tag isn't relevant to eg the kernel anyway
      throwNotSameShape e₁ e₂
    let t ← mergeExprs t₁ t₂
    let bd ← mergeExprs bd₁ bd₂
    let v ← withLetDecl n₁ t₁ bd fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprs v₁ v₂
      return v.abstract #[x]
    return .letE n₁ t bd v nonDep₁
  | .lam n₁ t₁ v₁ bi₁, .lam _n₂ t₂ v₂ bi₂ => do
    unless bi₁ == bi₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let t ← mergeExprs t₁ t₂
    let v ← withLocalDecl n₁ bi₁ t₁ fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprs v₁ v₂
      return v.abstract #[x]
    return .lam n₁ t v bi₁
  | .forallE n₁ t₁ v₁ bi₁, .forallE _n₂ t₂ v₂ bi₂ => do
    unless bi₁ == bi₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let t ← mergeExprs t₁ t₂
    let v ← withLocalDecl n₁ bi₁ t₁ fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprs v₁ v₂
      return v.abstract #[x]
    return .forallE n₁ t v bi₁
  | .mdata m₁ e₁, .mdata m₂ e₂ => do
    unless m₁ == m₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let e ← mergeExprs e₁ e₂
    return .mdata m₁ e
  | .app f₁ a₁, .app f₂ a₂ => do
    let f ← mergeExprs f₁ f₂
    let a ← mergeExprs a₁ a₂
    return .app f a
  | _,_ => throwNotSameShape e₁ e₂
