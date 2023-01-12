/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Basic
import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas

import Dijkstra.Control.Functor.Subreg

/-!
# Bishop finite types

A type `α` is called ***Bishop finite*** if it admits a surjection `Fin n → α` for some `n : Nat`.
Equivalently, `α` is Bishop finite if it admits a list `cover : List α` satisfying `∀ (a : α), a ∈ cover`.
-/

universe u


/-!
## Definition and instances
-/

/---
A type `α` is called ***Bishop finite*** if it admits a surjection `Fin n → α` for some `n : Nat`.
Equivalently, `α` is Bishop finite if it admits a list `cover : List α` satisfying `∀ (a : α), a ∈ cover`.
--/
class BishopFin (α : Type u) where
  cover : List α
  exhaustive : ∀ (a : α), a ∈ cover

/--- Every decidable subtype of a Bishop finite type is again Bishop finite -/
instance (α : Type u) [BishopFin α] (p : α → Prop) [DecidablePred p] : BishopFin (Subtype p) where
  cover := (BishopFin.cover (α:=α)).filterMap λ a =>
    if h : p a then some ⟨a,h⟩ else none
  exhaustive a := by
    cases a with | mk a ha =>
    suffices ∀ (l : List α), a ∈ l → Subtype.mk (p:=p) a ha ∈ l.filterMap λ a => if h : p a then some ⟨a,h⟩ else none
      from this (BishopFin.cover (α:=α)) (BishopFin.exhaustive a)
    intro l hal
    induction l
    case nil => cases hal
    case cons b l h_ind =>
      dsimp [List.filterMap]
      cases hal
      case head =>
        rw [dif_pos ha]; exact List.Mem.head _
      case tail htail =>
        by_cases p b
        case pos hpos =>
          rw [dif_pos hpos]
          exact List.Mem.tail _ (h_ind htail)
        case neg hneg =>
          rw [dif_neg hneg]
          exact h_ind htail


@[reducible]
protected
def Fin.elements (n : Nat) : List (Fin n) := aux n Nat.le.refl
  where
    aux : (k : Nat) → k ≤ n → List (Fin n)
    | 0, _ => []
    | k+1, h => ⟨k,h⟩ :: aux k (Nat.le_of_succ_le h)

instance (n : Nat) : BishopFin (Fin n) where
  cover := Fin.elements n
  exhaustive i := by
    suffices ∀ (k : Nat) (hk : k ≤ n) (j : Fin n), j.val < k → j ∈ Fin.elements.aux n k hk
      from this n Nat.le.refl i i.isLt
    intro k hk j hj
    induction k generalizing j
    case zero => cases hj
    case succ k h_ind =>
      cases hj
      case refl => exact List.Mem.head _
      case step hj =>
        apply List.Mem.tail _
        exact h_ind (Nat.le_of_succ_le hk) j hj

instance : BishopFin UInt8 where
  cover := UInt8.mk <$> Fin.elements UInt8.size
  exhaustive i :=
    match i with | UInt8.mk i => List.mem_map_of_mem UInt8.mk (BishopFin.exhaustive i)

instance : BishopFin UInt16 where
  cover := UInt16.mk <$> Fin.elements UInt16.size
  exhaustive i :=
    match i with | UInt16.mk i => List.mem_map_of_mem UInt16.mk (BishopFin.exhaustive i)

instance : BishopFin UInt32 where
  cover := UInt32.mk <$> Fin.elements UInt32.size
  exhaustive i :=
    match i with | UInt32.mk i => List.mem_map_of_mem UInt32.mk (BishopFin.exhaustive i)

instance : BishopFin UInt64 where
  cover := UInt64.mk <$> Fin.elements UInt64.size
  exhaustive i :=
    match i with | UInt64.mk i => List.mem_map_of_mem UInt64.mk (BishopFin.exhaustive i)


/-!
## Proof by exhaustive verification

If `α : Type u` is Bishop finite with, say, `BishopFin.cover (α:=α) ≡ [a₁,a₂,⋯]`, then given a predicate `p : α → Prop`, one can expect that the proposition `∀ a, p a` is proved by verifying `p a₁ ∧ p a₂ ∧ ⋯`.
For example, in the case `α ≡ Fin 3`, the proposition `∀ (i : Fin 3), p i` is exactly equivalent to `p 0 ∧ p 1 ∧ p 2`.
In the following, we implement a tactic for such a type of proofs.
-/

section proof_by_exhaust

namespace List

variable {α : Type u}

@[reducible]
protected
inductive forallr (p : α → Prop) : List α → Prop
| nil : List.forallr p []
| cons {head : α} {tail : List α} : p head → tail.forallr p → (head :: tail).forallr p

protected
theorem forallr_Mem {p : α → Prop} : {l : List α} → l.forallr p → ∀ a, a ∈ l → p a := by
  intro l hlp a hMem
  induction l
  case nil => cases hMem
  case cons hhead htail h_ind =>
    cases hMem
    case head => cases hlp; assumption
    case tail hMem => apply h_ind ?_ hMem; cases hlp; assumption

protected
theorem forallr_cover [BishopFin α] {p : α → Prop} : (BishopFin.cover (α:=α)).forallr p → ∀ a, p a :=
  λ hall a => List.forallr_Mem hall a (BishopFin.exhaustive a)

end List

open Lean Meta in
/--
To given mvar `?m` of type `List.forallr p l`, the function tries to unify
```lean
?mvar = List.forallr.cons ?m₁ (List.forallr.cons ?m₂ /-...-/ ?mtail)
```
using fresh mvars `#[?m₁, ?m2, ⋯]` and `?mtail` with `?mᵢ : p aᵢ` and `?mtail : List.forallr p tail` by case-matching `l = a₁ :: a₂ :: ⋯ :: tail`.
Note that if `tail = []`, then the mvar `?mtail` is automatically assigned to `List.forallr.nil`.
-/
partial def destructForallR (mvarId : MVarId) : MetaM (Array MVarId × Option MVarId) := do
  -- Make sure that the target type of the given mvar is of the form `List.forallr p l`.
  let (.app (.app (.app (.const ``List.forallr [uvar]) α) p) l) ← whnf (←mvarId.getType) | throwError "Failed to unify '{← mvarId.getType}' with 'List.forallr ?p ?l'."
  -- Unfold `List.forallr` recursively and generate mvars and a candidate expression that would be assinged to the target mvar.
  let (heads, tail?, e) ← loop uvar α p l
  -- Try assigning the computated expression to the target mvar.
  let .true ← isDefEq (.mvar mvarId) e | throwError "Failed to ensure '{e.dbgToString} : {(←mvarId.getType).dbgToString}'."
  if !(←mvarId.isAssigned) then mvarId.assign e
  -- Return the generated mvars.
  return (heads, tail?)
  where
    @[inline]
    loop (uvar : Level) (α p l : Expr) : MetaM (Array MVarId × Option MVarId × Expr) := do
      let l ← whnf l
      match l with
      | (.app (.app (.app (.const ``List.cons _) _) head) tail) => do
        -- Recurse to the tail
        let (heads, tailvarId?, etail) ← loop uvar α p tail
        -- Generate a fresh mvar for the head
        let headmvarId ← mkFreshExprMVar (some (.app p head))
        -- Combine head and tail to construct an expression
        let etail := mkAppN (.const ``List.forallr.cons [uvar]) #[
          α, p, head, tail, headmvarId, etail
        ]
        return (heads.push headmvarId.mvarId!, tailvarId?, etail)
      | (.app (.const ``List.nil _) _) =>
        -- If the list is empty, assign `List.forallr.nil`
        return (#[], none, mkAppN (.const ``List.forallr.nil [uvar]) #[α, p])
      | _ => do
        -- If the list is opaque, generate a fresh mvar for the whole remaining target.
        let tailmvarId ← mkFreshExprMVar (some (mkAppN (.const ``List.forallr [uvar]) #[α, p, l]))
        return (#[], tailmvarId.mvarId!, tailmvarId)

open Lean Meta Elab in
/--
Repeatedly apply given tactic on the head of a goal of the form `List.forall p l` as long as `l` can be decomposed.
-/
elab "decomp_forallr" tac:tactic : tactic =>
  Tactic.withMainContext do
    let goal::mvarIds ← Tactic.getUnsolvedGoals | Tactic.throwNoGoalsToBeSolved
    let (holes, htail?) ← destructForallR goal
    for hole in holes do
      try
        Tactic.setGoals [hole]
        Tactic.evalTactic tac
        Tactic.done
      catch _ => throwError "Failed to close the goal{indentExpr (← hole.getType)}"
    match htail? with
    | some htail => Tactic.setGoals (htail :: mvarIds)
    | none => Tactic.setGoals mvarIds

open Lean Meta Elab in
/--
For a predicate `p : α → Prop` on a Bishop finite type `α`, prove `∀ a, p a` by verifying `p a` for each entry `a : BishopFin.cover (α:=α)`.
Example:
```lean
example : ∀ (i j : Fin 20), i*j = j*i := by
  by_exhaust (by_exhaust (rfl))
```
@warning This tactic takes much log time when `BishopFin.cover` is huge (roughly, `length ∼ 1000`).
-/
elab "by_exhaust" tac:tactic : tactic =>
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    -- Destruct forallE to get the predicate
    let (.forallE nm t p _) ← whnf (←goal.getType) | throwError "Failed to unify '∀ (a : ?t), ?p' with{indentExpr (←goal.getType)}"
    let (.sort (.succ uvar)) ← inferType t | throwError "'Type u' expected:{indentExpr t} :{indentExpr (←inferType t)}"
    -- Make sure the type is Bishop finite
    let inst ← synthInstance (mkAppN (.const ``BishopFin [uvar]) #[t])
    -- Assign to the goal mvar `List.forallr_cover ?m`
    let lamp := Expr.lam nm t p .default
    let mvarId ← mkFreshExprMVar $ some $ mkAppN (.const ``List.forallr [uvar]) #[
      t, lamp, mkAppN (.const ``BishopFin.cover [uvar]) #[t, inst]
    ]
    let e := mkAppN (.const ``List.forallr_cover [uvar]) #[t, inst, lamp, mvarId]
    let .true ← isDefEq (.mvar goal) e | throwError "Failed to apply 'List.forallr_cover' to{indentExpr (←goal.getType)}"
    if !(←goal.isAssigned) then goal.assign e
    Tactic.replaceMainGoal [mvarId.mvarId!]
    Tactic.evalTactic (←`(tactic| decomp_forallr $tac:tactic))

end proof_by_exhaust

