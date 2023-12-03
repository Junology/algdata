/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Data.BinaryHeap.Basic

pkg_include Nat.foldRev_induction

/-!
# Heap condition

Given a comparison function `lt : α → α → Bool`, a tree is called a ***heap*** if each node is no less than its children have.
In particular, we discuss binary trees and prove that operations defined in `Algdata.Data.BinaryHeap.Hasic` respect the condition.

## Implementation note

For the indexing convention, see `Algdata.Data.BinaryHeap.Index`.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v


namespace Algdata.BinaryHeap

/-! ### Classes for comparison functions -/

section Class

variable {α : Type u}

/--
`LawfulLTBRel lt` ensures that a `Bool`-valued comparison function `lt : α → α → Bool` is suitable as an ordering on heaps.
Note that it is nearly equivalent to saying that `fun a b => lt a b = false` is a pre-order.

:::note info
If `lt` is a strict weak order, then it satisfies the two conditions.
-/
class LawfulLTBRel (lt : α → α → Bool) : Prop where
  /-- The comparison function is irreflexive. --/
  asymm {a b : α} : lt a b = true → lt b a = false
  /-- The negation of the comparison function is transitive. -/
  ntrans {a b c : α} : lt a b = false → lt b c = false → lt a c = false

instance _root_.Nat.lawfulLTBRel : LawfulLTBRel Nat.blt where
  asymm h := by
    simp only [Bool.eq_false_iff, Ne, Nat.blt_eq] at h ⊢
    exact Nat.lt_asymm h
  ntrans h₁ h₂ := by
    simp only [Bool.eq_false_iff, Ne, Nat.blt_eq, Nat.not_lt_eq] at h₁ h₂ ⊢
    exact Nat.le_trans h₂ h₁

namespace LawfulLTBRel

variable {lt : α → α → Bool} [LawfulLTBRel lt]

theorem irrefl (a : α) : lt a a = false :=
  match h : lt a a with
  | false => rfl
  | true => h.symm.trans (asymm h)

end LawfulLTBRel

end Class


/-!
### Heap condition
-/

/--
For `x : Subarray α` and `i : Nat`, `IsHeap x i` asserts that the subtree of `x` of `i` and its descendants satisfies the heap condition.
-/
inductive IsHeap {α : Type u} (lt : α → α → Bool) (x : Subarray α) : Nat → Prop where
| out_of_range (i : Nat) : i ≥ x.size → IsHeap lt x i
| node' (i : Nat) (_ : i < x.size) : ((_ : 2*i+1 < x.size) → lt x[i] x[2*i+1] = false) → ((_ : 2*i+2 < x.size) → lt x[i] x[2*i+2] = false) → IsHeap lt x (2*i+1) → IsHeap lt x (2*i+2) → IsHeap lt x i

namespace IsHeap

variable {α : Type u} (lt : α → α → Bool)

theorem leaf (x : Subarray α) (i : Nat) (hl : 2*i+1 ≥ x.size) : IsHeap lt x i := by
  if hi : i < x.size then
    have hr : 2*i+2 ≥ x.size := .step hl
    refine .node' i hi ?_ ?_ (.out_of_range _ hl) (.out_of_range _ hr)
    . intro hl'; exact absurd hl' (Nat.not_lt_of_le hl)
    . intro hr'; exact absurd hr' (Nat.not_lt_of_le hr)
  else
    exact .out_of_range i (Nat.ge_of_not_lt hi)

theorem node_odd (x : Subarray α) (i : Nat) (hl : 2*i+1 < x.size) (hr : 2*i+2 ≥ x.size) (hx : lt (x[i]'(Nat.lt_trans (lt_child_left i) hl)) x[2*i+1] = false) : IsHeap lt x i := by
  have hleft : IsHeap lt x (2*i+1) := by
    refine .leaf lt x _ (Nat.le_trans hr ?_)
    conv =>
      rhs
      rewrite [Nat.two_mul (2*i+1), Nat.add_assoc _ _ 1, Nat.add_comm (2*i+1) 1, ←Nat.add_assoc _ 1 _]
      change 2*i+2+(2*i+1)
    exact Nat.le_add_right (2*i+2) (2*i+1)
  have hright : IsHeap lt x (2*i+2) :=
    .out_of_range _ hr
  refine .node' i _ (fun _ => hx) ?_ hleft hright
  . intro hr'; exact absurd hr' (Nat.not_lt_of_le hr)

theorem node (x : Subarray α) (i : Nat) (hr : 2*i+2 < x.size) (hx₁ : lt (x[i]'(Nat.lt_trans (lt_child_right i) hr)) (x[2*i+1]'(Nat.lt_trans .refl hr)) = false) (hx₂ : lt (x[i]'(Nat.lt_trans (lt_child_right i) hr)) x[2*i+2] = false) (hleft : IsHeap lt x (2*i+1)) (hright : IsHeap lt x (2*i+2)) : IsHeap lt x i :=
  .node' i _ (fun _ => hx₁) (fun _ => hx₂) hleft hright

variable {lt}

theorem left {x : Subarray α} {i : Nat} (h : IsHeap lt x i) : IsHeap lt x (2*i+1) :=
  match i, h with
  | _, .out_of_range i h =>
    .out_of_range _ <| Nat.le_trans h (Nat.le_of_lt <| lt_child_left i)
  | _, .node' _ _ _ _ hleft _ => hleft

theorem right {x : Subarray α} {i : Nat} (h : IsHeap lt x i) : IsHeap lt x (2*i+2) :=
  match i, h with
  | _, .out_of_range i h =>
    .out_of_range _ <| Nat.le_trans h (Nat.le_of_lt <| lt_child_right i)
  | _, .node' _ _ _ _ _ hright => hright

theorem descend {x : Subarray α} {i j : Nat} (h : IsHeap lt x i) (hd : Descendant i j) : IsHeap lt x j := by
  induction hd with
  | refl => exact h
  | node_left j _ IH => exact IH h.left
  | node_right j _ IH => exact IH h.right

theorem of_subext {x y : Subarray α} {i : Nat} (h : IsHeap lt x i) (hsize : y.size ≤ x.size) (hext : ∀ (k : Nat) (hk : k < y.size), Descendant i k → y[k] = x[k]'(trans hk hsize :)) : IsHeap lt y i := by
  induction h with
  | out_of_range i hi =>
    exact .out_of_range i <| Nat.le_trans hsize hi
  | node' i _ lt_left lt_right _ _ IH₁ IH₂ =>
    specialize IH₁ fun k hk h => hext k hk (.node_left _ h)
    specialize IH₂ fun k hk h => hext k hk (.node_right _ h)
    if hiy : i < y.size then
      refine .node' i hiy ?_ ?_ IH₁ IH₂
      . intro hl
        rewrite [hext i hiy (.refl i), hext (2*i+1) hl (.child_left i)]
        exact lt_left <| Nat.lt_of_lt_of_le hl hsize
      . intro hr
        rewrite [hext i hiy (.refl i), hext (2*i+2) hr (.child_right i)]
        exact lt_right <| Nat.lt_of_lt_of_le hr hsize
    else
      exact .out_of_range i (Nat.le_of_not_lt hiy)

theorem not_lt_left {x : Subarray α} {i : Nat} (h : IsHeap lt x i) (hl : 2*i+1 < x.size) : lt (x[i]'(Nat.lt_trans (lt_child_left i) hl)) x[2*i+1] = false :=
  match i, h with
  | _, out_of_range i h =>
    absurd (Nat.lt_trans (lt_child_left i) hl) (Nat.not_lt_of_le h)
  | _, .node' i _ hleft _ _ _ => hleft hl

theorem not_lt_right {x : Subarray α} {i : Nat} (h : IsHeap lt x i) (hr : 2*i+2 < x.size) : lt (x[i]'(Nat.lt_trans (lt_child_right i) hr)) x[2*i+2] = false :=
  match i, h with
  | _, out_of_range i h =>
    absurd (Nat.lt_trans (lt_child_right i) hr) (Nat.not_lt_of_le h)
  | _, .node' i _ _ hright _ _ => hright hr

theorem not_lt_of_descendant [LawfulLTBRel lt] {x : Subarray α} {i : Nat} (h : IsHeap lt x i) (j : Nat) {hj : j < x.size} (hd : Descendant i j) : lt (x[i]'(Nat.lt_of_le_of_lt hd.le hj)) x[j] = false := by
  induction hd with
  | refl => exact LawfulLTBRel.irrefl _
  | node_left i hd IH =>
    exact LawfulLTBRel.ntrans (h.not_lt_left _) (IH h.left)
  | node_right i hd IH =>
    exact LawfulLTBRel.ntrans (h.not_lt_right _) (IH h.right)

theorem swap {x : Subarray α} {i : Nat} (h : IsHeap lt x i) (j₁ j₂ : Fin x.size) (hj₁ : j₁ < i) (hj₂ : j₂ < i) : IsHeap lt (x.swap j₁ j₂) i := by
  induction h with
  | out_of_range _ h => refine .out_of_range _ h
  | node' i hi hx₁ hx₂ _ _ IHl IHr =>
    specialize IHl (trans hj₁ (lt_child_left i)) (trans hj₂ (lt_child_left i))
    specialize IHr (trans hj₁ (lt_child_right i)) (trans hj₂ (lt_child_right i))
    refine node' i hi ?_ ?_ IHl IHr
    . intro hl; specialize hx₁ hl
      simp only [Subarray.getElem_swap]
      iterate rewrite [if_neg]
      exact hx₁
      all_goals apply Nat.ne_of_lt
      . exact trans hj₁ (lt_child_left i)
      . exact trans hj₂ (lt_child_left i)
      . exact hj₁
      . exact hj₂
    . intro hr; specialize hx₂ hr
      simp only [Subarray.getElem_swap]
      iterate rewrite [if_neg]
      exact hx₂
      all_goals apply Nat.ne_of_lt
      . exact trans hj₁ (lt_child_right i)
      . exact trans hj₂ (lt_child_right i)
      . exact hj₁
      . exact hj₂

theorem swap_left {x : Subarray α} {i : Fin x.size} (h : IsHeap lt x i.1) (j : Fin x.size) (hj : j.1 ≤ 2*i.1) : IsHeap lt (x.swap i j) (2*i.1+1) :=
  h.left.swap i j (lt_child_left i.1) (Nat.succ_le_succ hj)

theorem swap_right {x : Subarray α} {i : Fin x.size} (h : IsHeap lt x i.1) (j : Fin x.size) (hj : j.1 ≤ 2*i.1) : IsHeap lt (x.swap i j) (2*i.1+2) :=
  h.right.swap i j (lt_child_right i.1) (.step <| Nat.succ_le_succ hj)

#print axioms leaf
#print axioms node_odd
#print axioms node
#print axioms left
#print axioms right
#print axioms swap
#print axioms swap_left
#print axioms swap_right

end IsHeap


/-! ### The heap condition and `BinaryHeap.heapifyDown` -/

section HeapifyDown

variable {α : Type u} (lt : α → α → Bool) [LawfulLTBRel lt]

namespace heapifyDown.OpSpec

variable {lt} {x : Subarray α} {i : Nat} {y : Subarray α}

theorem not_lt_left (h : heapifyDown.OpSpec lt x i y) (hl : 2*i+1 < x.size) (heap_left : IsHeap lt x (2*i+1)) : lt (y[i]'(h.size_eq ▸ trans (lt_child_left i) hl)) (y[2*i+1]'(h.size_eq ▸ hl)) = false := by
  induction h with
  | node_next_left x i y hi _ hr hx' hx h _ =>
    rewrite [h.get_not_descendant i (fun h => Nat.not_lt_of_le h.le (lt_child_left i))]
    have ⟨k,hk,hdk,h⟩ := h.exists_get_descendant (2*i+1) hl (.refl  _)
    rewrite [Subarray.getElem_swap_left, h, Subarray.getElem_swap]
    if hlk : 2*i+1 = k then
      simp only [if_pos hlk]; exact LawfulLTBRel.asymm hx
    else
      simp only [if_neg hlk, if_neg <| Nat.ne_of_lt <| trans (lt_child_left i) hdk.le]
      exact heap_left.not_lt_of_descendant k hdk
  | node_end_left x i _ _ _ _ hx =>
    exact hx
  | node_next_right x i y hi _ hr hx' hx h _ =>
    rewrite [h.get_not_descendant i (fun h => Nat.not_lt_of_le h.le (lt_child_right i))]
    rewrite [h.get_not_descendant (2*i+1) (Descendant.sibling_not' i)]
    rw [Subarray.getElem_swap_left, Subarray.getElem_swap_ne, hx']
    . show i ≠ 2*i+1; exact Nat.ne_of_lt (lt_child_left i)
    . show 2*i+1+1 ≠ 2*i+1; exact Nat.ne_of_gt .refl
  | node_end_right x i hi _ hr hx' hx =>
    exact LawfulLTBRel.ntrans hx hx'
  | node_odd_next x i hi _ hr hx =>
    rewrite [Subarray.getElem_swap_left, Subarray.getElem_swap_right]
    exact LawfulLTBRel.asymm hx
  | node_odd_end x i _ _ _ hx =>
    exact hx
  | leaf x i  hl' => exact absurd hl <| Nat.not_lt_of_le hl'

theorem not_lt_right (h : heapifyDown.OpSpec lt x i y) (hr : 2*i+2 < x.size) (heap_right : IsHeap lt x (2*i+2)) : lt (y[i]'(h.size_eq ▸ trans (lt_child_right i) hr)) (y[2*i+2]'(h.size_eq ▸ hr)) = false := by
  induction h <;> try exact absurd hr <| Nat.not_lt_of_le ‹_›
  case node_next_left x i y hi hl _ hx' hx h _ =>
    rewrite [h.get_not_descendant i (fun h => Nat.not_lt_of_le h.le (lt_child_left i))]
    rewrite [h.get_not_descendant (2*i+2) (Descendant.sibling_not i)]
    rw [Subarray.getElem_swap_left, Subarray.getElem_swap_ne, LawfulLTBRel.asymm hx']
    . show i ≠ 2*i+2; exact Nat.ne_of_lt (lt_child_right i)
    . show 2*i+1 ≠ 2*i+1+1; exact Nat.ne_of_lt .refl
  case node_end_left x i _ _ _ hx' hx =>
    exact LawfulLTBRel.ntrans hx <| LawfulLTBRel.asymm hx'
  case node_next_right x i y hi hl _ hx' hx h _ =>
    rewrite [h.get_not_descendant i (fun h => Nat.not_lt_of_le h.le (lt_child_right i))]
    have ⟨k,hk,hdk,h⟩ := h.exists_get_descendant (2*i+2) hr (.refl _)
    rewrite [Subarray.getElem_swap_left, h, Subarray.getElem_swap]
    if hrk : 2*i+2 = k then
      simp only [if_pos hrk]; exact LawfulLTBRel.asymm hx
    else
      simp only [if_neg hrk, if_neg <| Nat.ne_of_lt <| trans (lt_child_right i) hdk.le]
      exact heap_right.not_lt_of_descendant k hdk
  case node_end_right x i hi _ _ hx' hx =>
    exact hx
  case leaf x i hl' =>
    exact absurd hr <| Nat.not_lt_of_le <| trans hl' (2*i+1).le_succ

theorem is_heap (h : heapifyDown.OpSpec lt x i y) (heap_left : IsHeap lt x (2*i+1)) (heap_right : IsHeap lt x (2*i+2)) : IsHeap lt y i := by
  let _hy_left := fun hl => h.not_lt_left hl heap_left
  let _hy_right := fun hr => h.not_lt_right hr heap_right
  induction h with
  | node_next_left x i y hi hl hr hx' hx h IH =>
    refine .node lt y i (h.size_eq ▸ hr) (_hy_left hl) (_hy_right hr) ?_ ?_
    . show IsHeap lt y (2*i+1)
      refine IH ?_ ?_
      . refine heap_left.left.swap _ _ ?_ (lt_child_left (2*i+1))
        exact trans (lt_child_left i) (lt_child_left (2*i+1))
      . refine heap_left.right.swap _ _ ?_ (lt_child_right (2*i+1))
        exact trans (lt_child_left i) (lt_child_right (2*i+1))
    . show IsHeap lt y (2*i+2)
      refine heap_right.of_subext (h.size_eq ▸ .refl) ?_
      intro k hk hdk
      rw [h.get_not_descendant k fun h => Descendant.sibling_not i <| h.ascend_right (.step .refl) hdk, Subarray.getElem_swap_ne]
      . exact Nat.ne_of_lt <| trans (lt_child_right i) hdk.le
      . exact Nat.ne_of_lt <| trans (2*i+1).lt_succ_self hdk.le
  | node_end_left x i _ hl hr hx' hx =>
    refine .node lt x i hr hx ?_ heap_left heap_right
    exact LawfulLTBRel.ntrans hx <| LawfulLTBRel.asymm hx'
  | node_next_right x i y hi hl hr hx' hx h IH =>
    refine .node lt y i (h.size_eq ▸ hr) (_hy_left hl) (_hy_right hr) ?_ ?_
    . show IsHeap lt y (2*i+1)
      refine heap_left.of_subext (h.size_eq ▸ .refl) ?_
      intro k hk hdk
      rw [h.get_not_descendant k fun h => Descendant.sibling_not i <| hdk.ascend_right (.step .refl) h, Subarray.getElem_swap_ne]
      . exact Nat.ne_of_lt <| trans (lt_child_left i) hdk.le
      . dsimp; intro h; cases h; exact absurd hdk (Descendant.sibling_not i)
    . show IsHeap lt y (2*i+2)
      refine IH ?_ ?_
      . refine heap_right.left.swap _ _ ?_ (lt_child_left (2*i+2))
        exact trans (lt_child_right i) (lt_child_left (2*i+2))
      . refine heap_right.right.swap _ _ ?_ (lt_child_right (2*i+2))
        exact trans (lt_child_right i) (lt_child_right (2*i+2))
  | node_end_right x i _ _ hr hx' hx =>
    exact .node lt x i hr (LawfulLTBRel.ntrans hx hx') hx heap_left heap_right
  | node_odd_next x i hi hl hr hx =>
    refine .node_odd lt _ i hl hr ?_
    rewrite [Subarray.getElem_swap_left, Subarray.getElem_swap_right]
    exact LawfulLTBRel.asymm hx
  | node_odd_end x i _ hl hr hx =>
    exact .node_odd lt x i hl hr hx
  | leaf x i hl => exact .leaf lt x i hl

end heapifyDown.OpSpec

theorem is_heap_heapifyDown (x : Subarray α) (i : Nat) (heap_left : IsHeap lt x (2*i+1)) (heap_right : IsHeap lt x (2*i+2)) : IsHeap lt (heapifyDown lt x i) i :=
  (heapifyDown.OpSpec.mk lt x i).is_heap heap_left heap_right

end HeapifyDown


/-! ### The heap condition and `BinaryHeap.mkHeap` -/

section MkHeap

variable {α : Type u} (lt : α → α → Bool) [LawfulLTBRel lt]

theorem is_heap_mkHeap (x : Subarray α) : IsHeap lt (mkHeap lt x) 0 := by
  rewrite [mkHeap_eq_foldRev]
  refine Nat.foldRev_induction (motive:=fun n x => ∀ k, n ≤ k → IsHeap lt x k) _ _ x ?_ ?_ 0 .refl
  . show ∀ k, x.size / 2 ≤ k → IsHeap lt x k
    intro k hk
    refine .leaf lt x k ?_
    rewrite [← Nat.div_add_mod x.size 2]
    refine Nat.add_le_add ?_ ?_
    . exact Nat.mul_le_mul_left 2 hk
    . apply Nat.le_of_succ_le_succ
      exact show x.size % 2 < 2 from Nat.mod_lt x.size (by decide)
  . show ∀ (n : Nat) (x : Subarray α), (∀ k, n+1 ≤ k → IsHeap lt x k) → ∀ k, n ≤ k → IsHeap lt (heapifyDown lt x n) k
    clear x; intro n x IH k hk
    if hk' : Descendant n k then
      suffices IsHeap lt (heapifyDown lt x n) n from
        this.descend hk'
      have : n ≤ 2 * n := by
        rewrite [Nat.two_mul]; exact Nat.le_add_left n n
      refine is_heap_heapifyDown lt x n ?_ ?_
      all_goals apply IH; apply Nat.succ_le_succ
      . exact this
      . exact .step this
    else
      have : n < k := Nat.lt_of_not_le fun h => by
        cases Nat.le_antisymm hk h
        exact hk' (.refl _)
      refine .of_subext (IH k this) (Nat.le_of_eq <| size_heapifyDown lt x _) ?_
      intro i hi hki
      suffices ¬ Descendant n i from
        get_heapifyDown_not_descendant lt x n i this
      intro hni
      exact hk' <| Descendant.ascend_right hk hni hki

end MkHeap


/-! ### The heap condition and `BinaryHeap.popMax` -/

section PopMax

variable {α : Type u} (lt : α → α → Bool) [LawfulLTBRel lt]

theorem IsHeap.popMax {x : Subarray α} (h : IsHeap lt x 0) : IsHeap lt (BinaryHeap.popMax lt x) 0 := by
  dsimp [BinaryHeap.popMax]
  if hsize : x.start < x.stop then
    simp only [dif_pos hsize]
    refine is_heap_heapifyDown lt _ 0 ?_ ?_
    . refine h.left.of_subext ?_ ?_
      . rewrite [Subarray.size_shrinkOne', Subarray.size_swap]; exact x.size.pred_le
      . intro k hk hki
        rewrite [Subarray.getElem_shrinkOne']
        refine Subarray.getElem_swap_ne _ _ _ k ?_ ?_
        . exact Nat.ne_of_lt hki.le
        . refine Nat.ne_of_gt <| Nat.lt_of_lt_of_le hk ?_
          simp only [Subarray.size_shrinkOne', Subarray.size_swap]
          exact .refl
    . refine h.right.of_subext ?_ ?_
      . rewrite [Subarray.size_shrinkOne', Subarray.size_swap]; exact x.size.pred_le
      . intro k hk hki
        refine Subarray.getElem_swap_ne _ _ _ k ?_ ?_
        . exact Nat.ne_of_lt <| Nat.lt_trans Nat.zero_lt_one hki.le
        . refine Nat.ne_of_gt <| Nat.lt_of_lt_of_le hk ?_
          simp only [Subarray.size_shrinkOne', Subarray.size_swap]
          exact .refl
  else
    simp only [dif_neg hsize]; exact h

end PopMax


/-! ### The proof that `heapSort` sorts a subarray-/

section HeapSort

variable {α : Type u} (lt : α → α → Bool) [LawfulLTBRel lt]

/-- The auxiliary condition assumed on the intermediate steps in `heapSort`. -/
private structure heapSort.Intermed (x : Subarray α) (stop : Nat) : Prop where
  stop_le : stop ≤ x.as.size
  is_heap : IsHeap lt x 0
  bound_above (i k : Nat) (hi : x.stop ≤ i ∧ i < stop) (hk : k < x.size) :
    lt (x.as[i]'(trans hi.2 stop_le :)) x[k] = false
  sorted (i j : Nat) (hi : x.stop ≤ i) (hij : i < j) (hj : j < stop) :
    lt (x.as[j]'(trans hj stop_le :)) (x.as[i]'(trans (trans hij hj) stop_le :)) = false

namespace heapSort.Intermed

theorem init (x : Subarray α) (h : IsHeap lt x 0) : Intermed lt x x.stop where
  stop_le := x.h₂
  is_heap := h
  bound_above _i _ hi _ :=
    absurd (trans hi.1 hi.2 :) x.stop.lt_irrefl
  sorted _i _ hi hij hj :=
    absurd (trans (trans hi hij) hj :) x.stop.lt_irrefl

protected theorem mkHeap (x : Subarray α) : Intermed lt (mkHeap lt x) (mkHeap lt x).stop :=
  init lt (mkHeap lt x) <| is_heap_mkHeap lt x

variable {lt} {x : Subarray α} {stop : Nat}

private theorem popMax (h : Intermed lt x stop) : Intermed lt (popMax lt x) stop where
  stop_le := size_as_popMax lt x ▸ h.stop_le
  is_heap := h.is_heap.popMax
  bound_above i k hi hk := by
    have ⟨k',hk',_ ,h⟩ := exists_get_popMax lt x k (size_popMax lt x ▸ hk)
    rewrite [h]; clear h
    have hrng : x.start < x.stop :=
      trans (x.start.le_add_left k') (Nat.add_lt_of_lt_sub hk')
    have hi' : x.stop - 1 ≤ i :=
      stop_popMax lt x hrng ▸ hi.1
    cases Nat.lt_or_eq_of_le hi' with
    | inl hlt =>
      have hi' : x.stop ≤ i :=
        Nat.sub_add_cancel (trans x.start.zero_le hrng :) ▸ hlt
      rewrite [get_as_popMax_of_ge_stop lt x i hi']
      exact h.bound_above i k' ⟨hi',hi.2⟩ hk'
    | inr heq =>
      cases heq
      rewrite [get_as_popMax_stop_sub_one lt x hrng]
      exact h.is_heap.not_lt_of_descendant k' (.root k')
  sorted i j hi hij hj := by
    cases Nat.lt_or_eq_of_le x.h₁ with
    | inl hrng =>
      simp only [stop_popMax lt x hrng] at hi
      have stop_pos : 0 < x.stop :=
        Nat.lt_of_le_of_lt x.start.zero_le hrng
      have : x.stop-1+1 = x.stop :=
        Nat.sub_add_cancel stop_pos
      have hj' : x.stop ≤ j :=
        trans this.symm (trans hi hij :)
      rewrite [get_as_popMax_of_ge_stop lt x j hj']
      cases Nat.lt_or_eq_of_le hi with
      | inl hlti =>
        have : x.stop ≤ i :=
          ‹x.stop-1+1=x.stop› ▸ (hlti : x.stop-1+1 ≤ i)
        rewrite [get_as_popMax_of_ge_stop lt x i this]
        exact h.sorted i j this hij hj
      | inr heqi =>
        cases heqi
        rewrite [get_as_popMax_stop_sub_one lt x hrng]
        exact h.bound_above j 0 ⟨hj',hj⟩ _
    | inr hz =>
      simp only [popMax_empty lt x hz] at hi ⊢
      exact h.sorted i j hi hij hj

private theorem of_spec {n : Nat} {y : Array α} (h : Intermed lt x stop) (h' : heapSort.loop.OpSpec lt x n y) (hn : n ≤ x.size) (i j : Nat) (hi : x.stop - n ≤ i) (hij : i < j) (hj : j < stop) : lt (y[j]'(h'.size_eq ▸ trans hj h.stop_le)) (y[i]'(h'.size_eq ▸ trans (trans hij hj) h.stop_le)) = false := by
  induction h' with
  | zero => exact h.sorted i j hi hij hj
  | @succ x n _ _ IH =>
    have : x.start < x.stop :=
      trans (x.start.le_add_left n) (Nat.add_lt_of_lt_sub hn)
    refine @IH h.popMax ?_ ?_
    . exact size_popMax lt x ▸ Nat.le_sub_of_add_le hn
    . rewrite [stop_popMax lt x this, Nat.sub_sub, Nat.add_comm]
      exact hi

end heapSort.Intermed

/-- The proof that `heapSort lt x` is sorted in the range `[x.start, x.stop]` in the sense that, for each `i j : Nat` in this range, `i < j` implies `lt x[j] x[i] = false` -/
theorem heapSort_spec (x : Subarray α) (i j : Nat) (hi : x.start ≤ i) (hij : i < j) (hj : j < x.stop) : lt ((heapSort lt x)[j]'(size_heapSort lt x ▸ trans hj x.h₂)) ((heapSort lt x)[i]'(size_heapSort lt x ▸ trans (trans hij hj :) x.h₂)) = false := by
  refine (heapSort.Intermed.mkHeap lt x).of_spec (.mk lt (mkHeap lt x) _) .refl i j ?_ hij ?_
  all_goals simp only [size_mkHeap, stop_mkHeap]
  . simp only [Subarray.size, Nat.sub_sub_self x.h₁]
    exact hi
  . exact hj

end HeapSort

end Algdata.BinaryHeap
