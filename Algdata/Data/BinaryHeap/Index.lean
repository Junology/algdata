/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

/-!
# Binary tree indexing

In this file, we discuss the binary tree structure on `Nat`, which plays a crucial role in the implementation of the binary heap (see `Algdata.Data.BinaryHeap.Basic`).

One can think of a positive integer `n` specifying a unique node in a binary tree in terms of its 2-adic representation; that is,

* `1` represents the root node;
* if `n` represents a node `X`, then `2*n` and `2*n+1` respectively represent the left and the right children of `X`.

For example, `n = 0b11001` represents ths right child of the left of the left of the right of the root node.

We translate this to `Nat` through the isomorphisms `(· + 1)` and `(· - 1)`.
An easy computation shows that, in this manner of indexing, `n : Nat` specifies a unique node in a binary tree so that

* `0` represents the root node;
* if `n` represents a node `X`, then `2*n+1` and `2*n+2` respectively represent the left and the right children of `X`.

Using this convention, one can think of an array `x : Array α` with `x.size = 10` as a binary tree depicted as follows:

- `x[0]`
  - `x[1]`
    - `x[3]`
      - `x[7]`
      - `x[8]`
    - `x[4]`
      - `x[9]`
  - `x[2]`
    - `x[5]`
    - `x[6]`

Note that this agrees with the breadth-first indexing.

-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false


namespace Algdata.BinaryHeap

/-! ### Auxiliary lemmas -/

@[simp]
theorem lt_child_left (i : Nat) : i < 2*i+1 := by
  rewrite [Nat.two_mul]
  exact Nat.succ_le_succ (i.le_add_left i)

@[simp]
theorem lt_child_right (i : Nat) : i < 2*i+2 :=
  .step (lt_child_left i)

@[simp]
theorem ge_parent (i : Nat) : i ≥ (i-1)/2 :=
  Nat.le_trans (Nat.div_le_self _ 2) i.pred_le

@[simp]
theorem gt_parent {i : Nat} (h : i > 0) : i > (i-1)/2 :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.pred_lt' h)


/-! ### Descendants nodes -/

/--
For `i j : Nat`, `Descendant i j` asserts that `j` is either a descendant of or equal to `i`.
In other words, `j` is an index of the subtree with root node `i`.
-/
inductive Descendant : Nat → Nat → Prop where
| refl (i : Nat) : Descendant i i
| node_left (i : Nat) {k : Nat} : Descendant (2*i+1) k → Descendant i k
| node_right (i : Nat) {k : Nat} : Descendant (2*i+2) k → Descendant i k

namespace Descendant

/--
The default induction principle on `Descendant i j`
It is essentially equivalent to the auto-generated recursor, but the `motive` is no longer dependent on the latter index (i.e. `j`).
-/
@[elab_as_elim, eliminator]
theorem induction_on
    {k : Nat} {motive : (i : Nat) → Descendant i k → Prop}
    {i : Nat} (h : Descendant i k)
    (refl : motive k (.refl k))
    (node_left : ∀ (i : Nat) (h : Descendant (2*i+1) k), motive (2*i+1) h → motive i (.node_left i h))
    (node_right : ∀ (i : Nat) (h : Descendant (2*i+2) k), motive (2*i+2) h → motive i (.node_right i h)) :
    motive i h := by
  induction h with
  | refl i => exact refl
  | node_left i h IH =>
    exact node_left i h <| IH refl node_left node_right
  | node_right i h IH =>
    exact node_right i h <| IH refl node_left node_right

theorem le : {i j : Nat} → Descendant i j → i ≤ j
| _, _, .refl i => .refl
| _, _, .node_left i h => trans (Nat.le_of_lt <| lt_child_left i) h.le
| _, _, .node_right i h => trans (Nat.le_of_lt <| lt_child_right i) h.le

theorem child_left (i : Nat) : Descendant i (2*i+1) :=
  .node_left i (.refl _)

theorem child_right (i : Nat) : Descendant i (2*i+2) :=
  .node_right i (.refl _)

theorem parent (i : Nat) : Descendant ((i-1)/2) i := by
  cases i with
  | zero => exact .refl 0
  | succ i =>
    rewrite [Nat.succ_sub_one, Nat.succ_eq_add_one]
    conv => rhs; rewrite [← Nat.div_add_mod i 2]
    cases i.mod_two_eq_zero_or_one with
    | inl hi_even =>
      rewrite [hi_even, Nat.add_zero]; exact .child_left _
    | inr hi_odd =>
      rewrite [hi_odd]; exact .child_right _

theorem trans {i j k : Nat} (hij : Descendant i j) (hjk : Descendant j k) : Descendant i k := by
  induction hij with
  | refl => exact hjk
  | node_left i _ IH => exact .node_left i IH
  | node_right i _ IH => exact .node_right i IH

theorem descend_left {i j : Nat} (h : Descendant i j) : Descendant i (2*j+1) :=
  h.trans (.child_left j)

theorem descend_right {i j : Nat} (h : Descendant i j) : Descendant i (2*j+2) :=
  h.trans (.child_right j)

theorem of_parent {i j : Nat} (h : Descendant i ((j-1)/2)) : Descendant i j :=
  h.trans (parent j)

/-- The right sibling node is not a descendant of the left; see also `Descendant.sibling_not'`. -/
theorem sibling_not (i : Nat) : ¬ Descendant (2*i+1) (2*i+2) := by
  intro h
  generalize hn : 2*i+1 = n at h
  cases h with
  | refl => cases Nat.add_left_cancel hn
  | node_left _ h =>
    cases hn; apply absurd h.le
    rewrite [Nat.two_mul (2*i+1), Nat.succ_le_succ_iff, Nat.add_le_add_iff_left (m:=0)]
    exact (2*i).not_lt_zero
  | node_right _ h =>
    cases hn; apply absurd h.le
    rewrite [Nat.two_mul (2*i+1), Nat.add_le_add_iff_right]
    conv => rhs; rhs; change 2*i+0
    rewrite [Nat.add_assoc, Nat.add_le_add_iff_left, Nat.add_comm 1]
    exact (2*i+1).not_lt_zero

/-- The left sibling node is not a descendant of the right; see also `Descendant.sibling.not`. -/
theorem sibling_not' (i : Nat) : ¬ Descendant (2*i+2) (2*i+1) := by
  intro h; apply absurd h.le
  rewrite [Nat.add_le_add_iff_left]
  decide

theorem irrel_descend {i j k : Nat} (hij : Descendant i j) (hik : ¬ Descendant i k) : ¬ Descendant j k :=
  fun h => hik (hij.trans h)

/-- If `j` is a descendant of `i`, then the parent of `j` is a descendant of that of `i`. -/
theorem ascend {i j : Nat} (h : Descendant i j) : Descendant ((i-1)/2) ((j-1)/2) := by
  induction h with
  | refl => exact .refl _
  | node_left i' _ IH =>
    rewrite [Nat.succ_sub_one, Nat.mul_div_right _ (by decide)] at IH
    exact .trans (.parent i') IH
  | node_right i' _ IH =>
    rewrite [Nat.succ_sub_one, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide)] at IH
    conv at IH =>
      lhs; change 0 + i'; rewrite [Nat.zero_add]
    exact .trans (.parent i') IH

theorem ascend_left_parent {i j : Nat} (h : Descendant i j) : Descendant ((i-1)/2) j :=
  .trans h.ascend (.parent j)

/-- If `j` is a dscendant of `i`, and if `i < j`, then the parent of `j` is also a descendant of `i`. -/
theorem ascend_right_parent {i j : Nat} (h : Descendant i j) (hij : i < j) : Descendant i ((j-1)/2) := by
  induction h with
  | refl => exact absurd hij j.lt_irrefl
  | node_left i h =>
    have := h.ascend
    rewrite [Nat.succ_sub_one, Nat.mul_div_right _ (by decide)] at this
    exact this
  | node_right i h =>
    have := h.ascend
    conv at this =>
      rw [Nat.succ_sub_one, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide)]
      lhs; change 0 + i; rw [Nat.zero_add]
    exact this

theorem ascend_right {i j k : Nat} (hij : i ≤ j) (hik : Descendant i k) (hjk : Descendant j k) : Descendant i j := by
  induction hjk with
  | refl => exact hik
  | node_left j _ IH =>
    specialize IH (Nat.le_trans hij (Nat.le_of_lt <| (lt_child_left j)))
    have := IH.ascend_right_parent (Nat.lt_of_le_of_lt hij (lt_child_left j))
    rewrite [Nat.succ_sub_one, Nat.mul_div_right _ (by decide)] at this
    exact this
  | node_right j _ IH =>
    specialize IH (Nat.le_trans hij (Nat.le_of_lt <| (lt_child_right j)))
    have := IH.ascend_right_parent (Nat.lt_of_le_of_lt hij (lt_child_right j))
    conv at this =>
      rhs; rw [Nat.succ_sub_one, Nat.add_comm, Nat.add_mul_div_left 1 j (by decide)]
      change 0 + j; rw [Nat.zero_add]
    exact this

/-- `Descendant` is a total relation on the set of ascendants of each node; i.e. on `{i // Descendant i k}` for each `k : Nat`. -/
theorem ascendants_total {i j k : Nat} (hik : Descendant i k) (hjk : Descendant j k) : Descendant i j ∨ Descendant j i := by
  cases Nat.lt_or_ge i j with
  | inl hlt => exact Or.inl <| ascend_right (Nat.le_of_lt hlt) hik hjk
  | inr hge => exact Or.inr <| ascend_right hge hjk hik

theorem root (i : Nat) : Descendant 0 i := by
  induction i using Nat.strongInductionOn
  rename_i i IH
  cases Nat.eq_zero_or_pos i with
  | inl hz => cases hz; exact .refl 0
  | inr hpos =>
    specialize IH ((i-1)/2) (gt_parent hpos)
    exact .trans IH (.parent i)

instance decidable (i j : Nat) : Decidable (Descendant i j) :=
  if hlt : i < j then
    have : (j-1)/2 < j :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ 2) (Nat.pred_lt' hlt)
    match decidable i ((j-1)/2) with
    | .isTrue IH => .isTrue IH.of_parent
    | .isFalse IH =>
      .isFalse fun h => IH (h.ascend_right_parent hlt)
  else if heq : i = j then
    .isTrue <| heq ▸ .refl i
  else
    .isFalse fun h =>
      heq <| Nat.le_antisymm h.le (Nat.le_of_not_lt hlt)
termination_by _ => j

end Descendant

end Algdata.BinaryHeap
