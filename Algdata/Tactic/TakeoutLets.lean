/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Tactic.Basic

/-!
# Extraction and introduction of `let` and `let_fun`

This module defines two tactics `takeout_lets` and `intro_let` that respectively take out nested `let`s (and `let_fun`s as well) from an expressions and introduce one to the local context.

One of the expected use cases is as follows.
Suppose we have a function like this:

```lean
def getLeft (l : List Nat) (i j : Nat) (hi : i < l.length) (hj : j < l.length) : Nat :=
  let k := if i < j then i else j
  have : k < l.length := by dsimp; split <;> assumption
  l[k]
```

Consider proving some properties of `getLeft` function; such as

```lean
example : getLeft [0,1,2,3] 3 2 (by decide) (by decide) = 2 := by
  sorry
```

The problem here is that `let k := ...` expression in the def of `getLeft` is so long that the zeta-reduction messes up the goal state of the theorem.
This is where `takeout_lets` is useful:

```lean
example : getLeft [0,1,2,3] 3 2 (by decide) (by decide) = 2 := by
  unfold getLeft
  /-
  goal state:
  > ⊢ (let k := if 3 < 2 then 3 else 2;
  > let_fun this := (_ : (if 3 < 2 then 3 else 2) < List.length [0, 1, 2, 3]);
  > [0, 1, 2, 3][k]) =
  > 2
  -/
  takeout_lets
  /-
  goal state:
  > ⊢ let k := if 3 < 2 then 3 else 2;
  > let_fun this := (_ : (if 3 < 2 then 3 else 2) < List.length [0, 1, 2, 3]);
  > [0, 1, 2, 3][k] = 2
  -/
  iterate intro_let
  /-
  goal state:
  k : Nat := if 2 < 3 then 2 else 3
  this : k < List.length [3, 1, 4, 1, 5]
  ⊢ [3, 1, 4, 1, 5][k] = 4
  -/
  sorry
```

In this example, you see that `takeout_lets` tactic takes `let` and `let_fun` binders out to the expression of the goal.
Finally, the `let` and `let_fun` binders are moved to the local context by `intro_let` tactic.
-/

set_option autoImplicit false

open Lean Meta

namespace Algdata

universe u

/--
Take `let` binders out of a given expression; e.g. the expression for `(let x := 2; let y : Fin (x+1) := ⟨x,x.lt_succ_self⟩; x + y.1) = 2 * (let z := 2; z)` would become `let x := 2; let y : Fin (x+1) := ⟨x,x.lt_succ_self⟩; let z := 2; x + y.1 = 2 * z`.
In order to avoid difficulties, the function does not enter into the bodies of the lambda expressions and the Pi types.

If `letFun = true`, then the function also treat `let_fun` expression (i.e. `(fun x => b) v`) as well.
In this case, the bound value of `let_fun` expression (i.e. `v` in `let_fun x := v; b`) is preserved.
This is because `let_fun` is mainly used to bind proofs of propositions (via `have`-expression)  so that one is not really interested in their actual values.
-/
def takeoutLets (e : Expr) (letFun : Bool := true) : Expr :=
  match e with
  | .app e₁ e₂ =>
    let e₁ := takeoutLets e₁ letFun
    let e₂ := takeoutLets e₂ letFun
    e₁ |> takeout fun k₁ e₁ =>
      e₂ |> takeout fun k₂ e₂ =>
        .app (e₁.liftLooseBVars 0 k₂) (e₂.liftLooseBVars k₂ k₁)
  | .lam name ty e binfo =>
    let ty := takeoutLets ty letFun
    ty |> takeout fun kt ty => .lam name ty (e.liftLooseBVars 1 kt) binfo
  | .forallE name ty e binfo =>
    let ty := takeoutLets ty letFun
    ty |> takeout fun _ ty => .forallE name ty e binfo
  | .letE name ty val body dinfo =>
    let ty := takeoutLets ty letFun
    let val := takeoutLets val letFun
    let body := takeoutLets body letFun
    ty |> takeout fun kt ty =>
      val |> takeout fun kv val =>
        .letE name (ty.liftLooseBVars 0 kv) (val.liftLooseBVars kv kt) (body.liftLooseBVars 1 (kt+kv)) dinfo
  | .mdata md e =>
    if letFun && isLetFun (.mdata md e) then
      match e with
      | .app (.lam n ty body binfo) val =>
        let ty := takeoutLets ty letFun
        let body := takeoutLets body letFun
        ty |> takeout fun kt ty =>
          mkLetFunAnnotation <| .app (.lam n ty (body.liftLooseBVars 1 kt) binfo) val
      | e => panic! s!"Invalid let_fun expression {e}"
    else
      takeout (fun _ => Expr.mdata md) (takeoutLets e letFun)
  | .proj name i e =>
    takeout (fun _ => Expr.proj name i) (takeoutLets e letFun)
  | e => e
where
  takeout (f : Nat → Expr → Expr) : Expr → optParam Nat 0 → Expr
  | .letE name ty val body isdep, k =>
    let body := takeout f body (k+1)
    .letE name ty val body isdep
  | .mdata md e, k =>
    if letFun && isLetFun (.mdata md e) then
      match e with
      | .app (.lam n t body binfo) val =>
        let body := takeout f body (k+1)
        mkLetFunAnnotation <| .app (.lam n t body binfo) val
      | e => panic! s!"Invalid let_fun expression {e}"
    else
      f k (.mdata md e)
  | e, k => f k e

/--
Move a local declaration binder in the target type to the local context.
More precisely,

* if the proof state is of the form `ctx ⊢ let name : type := val; goal`, then the new state would be `ctx(, name : type := val)? ⊢ goal` where new declaration `name` is not created if there is a local declaration in `ctx` with name `name` and `withReducible isDefEq` to `val`;
* if the proof state is of the form `ctx ⊢ let_fun name : type := val; goal`, then the new state would be `ctx(, name : type)? ⊢ goal` where new local variable `name` is not created either
  * `type` is a proposition and there is a local variable in `ctx` with the same name and the same type (with respect to `withReducible isDefEq`), or
  * there is a local declaration in `ctx` with the same name and `withReducible isDefEq` to `val`.
-/
def introLet1 (mvarId : MVarId) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `intro_let
    let lctx ← getLCtx
    match consumeMD (← mvarId.getType) with
    | .letE name ty val body _ =>
      match (← find lctx name ty val) with
      | .some fvarId =>
        mvarId.change <| body.instantiate1 (.fvar fvarId)
      | .none =>
        let ⟨_, mvarId⟩ ← mvarId.intro1P
        return mvarId
    | .mdata md e =>
      let .app (.lam name ty body binfo) val := e
        | throwError "Invalid 'let_fun' expression: {Expr.mdata md e}"
      match (← find lctx name ty val) with
      | .some fvarId =>
        mvarId.change <| body.instantiate1 (.fvar fvarId)
      | .none =>
        let newType : Expr := .forallE name ty body binfo
        let newMVar ← mkFreshExprSyntheticOpaqueMVar newType (← mvarId.getTag)
        mvarId.assign (.app newMVar val)
        let ⟨_, newMVarId⟩ ← newMVar.mvarId!.intro1P
        return newMVarId
    | t =>
      throwError "The target expression is neighter 'let' nor 'let_fun': {t}"
where
  consumeMD : Expr → Expr
    | .mdata md e =>
      if (md.size == 1) && (md.getBool `let_fun false) then
        .mdata md e
      else
        consumeMD e
    | e => e
  find (lctx : LocalContext) (name : Name) (ty val : Expr) : MetaM (Option FVarId) := do
    match lctx.findFromUserName? name with
    | .some (.cdecl _ fvarId _ ty' _ _) =>
      if (← isProp ty) && (ty == ty') then
        return .some fvarId
      else
        return .none
    | .some (.ldecl _ fvarId _ ty' val' _ _) =>
      if (ty == ty') && (val == val') then
        return .some fvarId
      else
        return .none
    | .none => return .none

open Elab Tactic

/--
Take `let` binders out of a given expression; e.g. the expression for `(let x := 2; let y : Fin (x+1) := ⟨x,x.lt_succ_self⟩; x + y.1) = 2 * (let z := 2; z)` would become `let x := 2; let y : Fin (x+1) := ⟨x,x.lt_succ_self⟩; let z := 2; x + y.1 = 2 * z`.
In order to avoid difficulties, the tactic does not enter into the bodies of the lambda expressions and the Pi types.
-/
elab "takeout_lets" : tactic =>
  withMainContext do
    liftMetaTactic1 fun mvarId =>
      mvarId.modifyTarget (pure ∘ takeoutLets)

@[inherit_doc introLet1]
elab "intro_let" : tactic =>
  withMainContext do
    liftMetaTactic1 fun mvarId =>
      introLet1 mvarId

end Algdata
