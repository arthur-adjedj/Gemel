module

public meta import LeanALaCarte.Elab
import Lean.Meta.Basic
open Lean Meta
public meta section


def throwNotSameShape (e₁ e₂ : Expr) : CoreM α :=
  throwError "The following terms do not have the same shape, and thus cannot be merged: {indentExpr e₁} {indentExpr e₂}"

-- For now, the algorithm is really naive and merges exprs 2 by 2. Once this is stable and works well enough, we can optimise this function to take an array of exprs instead, and match on the first one.
partial def mergeExprsBin (e₁ e₂ : Expr) : ModularM Expr :=
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
    let some matchers₁ := exts.get? m | fallback ()
    let some matchers₂ := exts.get? m' | fallback ()
    modifyMatchExtensions (· |>.erase m' |>.insert m (matchers₁ ++ matchers₂))
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
    let e ← mergeExprsBin struct₁ struct₂
    return .proj tyName₁ idx₁ e
  | .letE n₁ t₁ bd₁ v₁ nonDep₁ , .letE _n₂ t₂ bd₂ v₂ nonDep₂ => do
    unless nonDep₁ == nonDep₂ do --too strict ? this tag isn't relevant to eg the kernel anyway
      throwNotSameShape e₁ e₂
    let t ← mergeExprsBin t₁ t₂
    let bd ← mergeExprsBin bd₁ bd₂
    let v ← withLetDecl n₁ t₁ bd fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprsBin v₁ v₂
      return v.abstract #[x]
    return .letE n₁ t bd v nonDep₁
  | .lam n₁ t₁ v₁ bi₁, .lam _n₂ t₂ v₂ bi₂ => do
    unless bi₁ == bi₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let t ← mergeExprsBin t₁ t₂
    let v ← withLocalDecl n₁ bi₁ t₁ fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprsBin v₁ v₂
      return v.abstract #[x]
    return .lam n₁ t v bi₁
  | .forallE n₁ t₁ v₁ bi₁, .forallE _n₂ t₂ v₂ bi₂ => do
    unless bi₁ == bi₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let t ← mergeExprsBin t₁ t₂
    let v ← withLocalDecl n₁ bi₁ t₁ fun x => do
      let v₁ := v₁.instantiate1 x
      let v₂ := v₂.instantiate1 x
      let v ← mergeExprsBin v₁ v₂
      return v.abstract #[x]
    return .forallE n₁ t v bi₁
  | .mdata m₁ e₁, .mdata m₂ e₂ => do
    unless m₁ == m₂ do -- do we care ?
      throwNotSameShape e₁ e₂
    let e ← mergeExprsBin e₁ e₂
    return .mdata m₁ e
  | .app f₁ a₁, .app f₂ a₂ => do
    let f ← mergeExprsBin f₁ f₂
    let a ← mergeExprsBin a₁ a₂
    return .app f a
  | _,_ => throwNotSameShape e₁ e₂

def mergeExprs (es : Array Expr) : ModularM Expr := do
  if es.isEmpty then
    throwError "Unexpected, "
  if es.size = 1 then
    return es[0]!
  let mut res := es[0]!
  for e₂ in es[1:] do
    res ← mergeExprsBin res e₂
  return res
