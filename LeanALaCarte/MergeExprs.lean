module

public meta import LeanALaCarte.Elab
public import LeanALaCarte.Elab
open Lean Meta
public meta section


partial def getDelayedMVarRoot' [Monad m] [MonadMCtx m] (mvarId : MVarId) : m (MVarId × Nat) := do
  match (← getDelayedMVarAssignment? mvarId) with
  | some d => do
    let (m,n) ← getDelayedMVarRoot' d.mvarIdPending
    return (m,n+d.fvars.size)
  | none   => return (mvarId,0)

def throwNotSameShape (e₁ e₂ : Expr) : CoreM α :=
  throwError "The following terms do not have the same shape, and thus cannot be merged: {indentExpr e₁} {indentExpr e₂}"

-- For now, the algorithm is really naive and merges exprs 2 by 2. Once this is stable and works well enough, we can optimise this function to take an array of exprs instead, and match on the first one.
partial def mergeExprsBin (e₁ e₂ : Expr) : ModularM Expr :=
  withIncRecDepth do
  withTraceNode `Modular.Merge (λ exn => withModMappedLCtx do return m!"mergeExprsBin {indentExpr e₁} {indentExpr e₂} \n⇒{← (return exn.toOption.map indentExpr)}") do
  e₁.withApp fun fn₁ args₁ => do
  e₂.withApp fun fn₂ args₂ => do
  match fn₁,fn₂ with
  | .mvar m₁, .mvar m₂ => do
    let (m₁,_) ← getDelayedMVarRoot' m₁
    let (m₂,_) ← getDelayedMVarRoot' m₂
    let args ← mergeArgs args₁ args₂
    let exts ← getMatchExtensions
    let some matchers₁ := exts.get? m₁
      | trace[Modular.Merge] "{Expr.mvar m₁} is not a matcher"
        return (mkAppN fn₂ args)
    let some matchers₂ := exts.get? m₂
      | trace[Modular.Merge] "{Expr.mvar m₂} is not a matcher"
        return (mkAppN fn₁ args)
    trace[Modular.Merge] "Merging matchers {matchers₁.map fun {matchName, mvar,..} => (matchName,Expr.mvar mvar)} and {matchers₂.map fun {matchName, mvar,..} => (matchName,Expr.mvar mvar)}}"
    modifyMatchExtensions (· |>.erase m₂ |>.insert m₁ (matchers₁ ++ matchers₂))
    return (mkAppN fn₁ args)
  | .mvar _, _  =>
    return e₂
      -- let (_,n₁) ← getDelayedMVarRoot' m₁
      -- trace[Modular.Merge] "number of delayed-assign args:"
      -- let n₂ := args₁.size - n₁
      -- assert! n₂ >= args₂.size
      -- let args ← mergeArgs args₁[n₁:] args₂[:n₂]
      -- let res := mkAppN fn₂ args
      -- return res
  | _,.mvar _  =>
    return e₁
      -- let (_,n₂) ← getDelayedMVarRoot' m₂
      -- let n₁ := args₂.size - n₂
      -- assert! n₁ >= args₁.size
      -- let args ← mergeArgs args₁[n₁:] args₂[:n₂]
      -- let res := mkAppN fn₁ args
      -- return res
  | _,_ => return mkAppN (← traverse fn₁ fn₂) (← mergeArgs args₁ args₂)

where
  @[inline]
  mergeArgs (args₁ args₂ : Array Expr) := do
    unless args₁.size = args₂.size do
      throwError "Unexpected when merging exprs: not the same number of arguments: \n{args₁}\n{args₂} "
    args₁.zipWithM (bs := args₂) mergeExprsBin

  traverse (e₁ e₂ : Expr) : ModularM Expr :=
  match e₁, e₂ with
  | .bvar _, .bvar _
  | .fvar _, .fvar _
  | .lit _, .lit _
  | .const .., .const ..
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
