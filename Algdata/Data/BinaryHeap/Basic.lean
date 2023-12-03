/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Tactic.TakeoutLets
import Algdata.Data.Array.Lemmas
import Algdata.Data.Array.Subarray
import Algdata.Data.BinaryHeap.Index

/-!
# Binary heap

We implement a simple binary heap on array-like structures with respect to a comparison function `lt : α → α → Bool` using binary heaps.

## Main declarations

* `heapfyDown`: push a node down to the subtree to maintain the heap condition

## Implementation details

The codes are based on the ones in `Mathlib.Data.BinaryHeap`.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v w ww

namespace Algdata.BinaryHeap

variable {α : Type u} (lt : α → α → Bool)


/-! ### Declarations about `BinaryHeap.heapifyDown` -/

@[inline]
unsafe def heapifyDownUnsafeCore (x : Array α) (start size i : USize) : Array α :=
  let rec @[specialize] loop (x : Array α) (i : USize) : Array α :=
    let lhs := 2*i + 1
    let rhs := lhs + 1
    if rhs < size then
      let j : USize :=
        if lt (x.uget (start + rhs) lcProof) (x.uget (start + lhs) lcProof) then lhs else rhs
      if lt (x.uget (start + i) lcProof) (x.uget (start + j) lcProof) then
        loop (x.uswap (start + i) (start + j) lcProof lcProof) j
      else
        x
    else if lhs < size then
      if lt (x.uget (start + i) lcProof) (x.uget (start + lhs) lcProof) then
        x.uswap (start + i) (start + lhs) lcProof lcProof
      else
        x
    else x
  loop x i

/-- Unsafe implementation of `BinaryHeap.heapifyDown`. -/
@[inline]
unsafe def heapifyDownUnsafe (x : Subarray α) (i : @& Nat) : Subarray α :=
  let ⟨x, start, stop, _, _⟩ := x
  let ustart : USize := start.toUSize
  let usize : USize := stop.toUSize - ustart
  ⟨heapifyDownUnsafeCore lt x ustart usize i.toUSize, start, stop, lcProof, lcProof⟩


/--
Push a node `i` in `x` down to the subtree so that if its proper subtrees satisfy the heap condition, then the result tree does from the node `i`.
In spite of its specification, the function does not take `IsHeap` as an argument; see `heap_heapifyDown`.

See also `BinaryHeap.heapifyDown` in `Mathlib.Data.BinaryHeap`.

* Implementation note
  Currently, `heapifyDown` is an abbreviation by `heapifyDownAux` to avoid the bug in [lean4#2899](https://github.com/leanprover/lean4/issues/2899).
-/
def heapifyDownAux (x : Subarray α) (i : Nat) : Subarray α :=
  let lhs := 2*i + 1 -- The index of the left child
  let rhs := lhs + 1   -- The index of the right child
  if hr : rhs < x.size then
    have hi : i < x.size := trans (lt_child_right i) hr
    have hl : lhs < x.size := trans lhs.lt_succ_self hr
    -- Choose one of `lhs` and `rhs` whose value is not less than the other.
    -- We prefer `rhs` to `lhs` becuse of the expected number of comparison.
    let j : Nat := if lt x[rhs] x[lhs] then lhs else rhs
    have hj : i < j ∧ j < x.size := by
      if h : lt x[rhs] x[lhs] then
        dsimp; rewrite [if_pos h]; exact ⟨lt_child_left i, hl⟩
      else
        dsimp; rewrite [if_neg h]; exact ⟨lt_child_right i, hr⟩
    if lt x[i] (x[j]'hj.2) then
      -- This claim is necessary to prove the termination
      have : x.size - j < x.size - i :=
        Nat.sub_lt_sub_left hi hj.1
      -- Push the current node down to the subtree
      heapifyDownAux (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j
    else
      x
  else if hl : lhs < x.size then
    have hi : i < x.size := trans (lt_child_left i) hl
    -- In this case, `lhs` is the unique child of `i` with no children.
    if lt x[i] x[lhs] then x.swap ⟨i,hi⟩ ⟨lhs,hl⟩ else x
  else
    x
termination_by _ => x.size - i

@[inherit_doc heapifyDownAux, implemented_by heapifyDownUnsafe]
abbrev heapifyDown (x : Subarray α) (i : @& Nat) : Subarray α :=
  heapifyDownAux lt x i

/-- The `heapifyDown lt x i y` asserts that `y = heapifyDown lt x i` in the operational semantic manner. -/
protected inductive heapifyDown.OpSpec : Subarray α → Nat → Subarray α → Prop where
| node_next_left : ∀ (x : Subarray α) (i : Nat) (y : Subarray α) (hi : i < x.size) (hl : 2*i+1 < x.size) (hr : 2*i+2 < x.size), lt x[2*i+2] x[2*i+1] = true → lt x[i] x[2*i+1] = true → heapifyDown.OpSpec (x.swap ⟨i,hi⟩ ⟨2*i+1,hl⟩) (2*i+1) y → heapifyDown.OpSpec x i y
| node_end_left : ∀ (x : Subarray α) (i : Nat) (hi : i < x.size) (hl : 2*i+1 < x.size) (hr : 2*i+2 < x.size), lt x[2*i+2] x[2*i+1] = true → lt x[i] x[2*i+1] = false → heapifyDown.OpSpec x i x
| node_next_right : ∀ (x : Subarray α) (i : Nat) (y : Subarray α) (hi : i < x.size) (hl : 2*i+1 < x.size) (hr : 2*i+2 < x.size), lt x[2*i+2] x[2*i+1] = false → lt x[i] x[2*i+2] = true → heapifyDown.OpSpec (x.swap ⟨i,hi⟩ ⟨2*i+2,hr⟩) (2*i+2) y → heapifyDown.OpSpec x i y
| node_end_right : ∀ (x : Subarray α) (i : Nat) (hi : i < x.size) (hl : 2*i+1 < x.size) (hr : 2*i+2 < x.size), lt x[2*i+2] x[2*i+1] = false → lt x[i] x[2*i+2] = false → heapifyDown.OpSpec x i x
| node_odd_next : ∀ (x : Subarray α) (i : Nat) (hi : i < x.size) (hl : 2*i+1 < x.size), 2*i+2 ≥ x.size → lt x[i] x[2*i+1] = true → heapifyDown.OpSpec x i (x.swap ⟨i,hi⟩ ⟨2*i+1,hl⟩)
| node_odd_end : ∀ (x : Subarray α) (i : Nat) (hi : i < x.size) (hl : 2*i+1 < x.size), 2*i+2 ≥ x.size → lt x[i] x[2*i+1] = false → heapifyDown.OpSpec x i x
| leaf : ∀ (x : Subarray α) (i : Nat), 2*i+1 ≥ x.size → heapifyDown.OpSpec x i x


namespace heapifyDown.OpSpec

protected theorem mk (x : Subarray α) (i : Nat) : heapifyDown.OpSpec lt x i (heapifyDown lt x i) := by
  unfold heapifyDown heapifyDownAux
  takeout_lets; intro_let; intro_let
  if hr : rhs < x.size then
    simp (config:={zeta:=false,beta:=false}) only [dif_pos hr]
    takeout_lets; iterate intro_let
    have _hdecreasing := ‹x.size - j < x.size - i›
    have IH := OpSpec.mk (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j
    if hx' : lt x[rhs] x[lhs] then
      have hjl : j = lhs := if_pos hx'
      simp (config:={zeta:=false}) only [hjl] at IH ⊢
      if hx : lt x[i] x[lhs] then
        simp only [if_pos hx]
        exact node_next_left x i _ hi hl hr hx' hx IH
      else
        simp only [if_neg hx]
        exact node_end_left x i hi hl hr hx' (Bool.of_not_eq_true hx)
    else
      have hjr : j = rhs := if_neg hx'
      simp (config:={zeta:=false}) only [hjr] at IH ⊢
      if hx : lt x[i] x[rhs] then
        simp only [if_pos hx]
        exact node_next_right x i _ hi hl hr (Bool.of_not_eq_true hx') hx IH
      else
        simp only [if_neg hx]
        exact node_end_right x i hi hl hr (Bool.of_not_eq_true hx') (Bool.of_not_eq_true hx)
  else if hl : lhs < x.size then
    simp (config:={zeta:=false,beta:=false}) only [dif_neg hr, dif_pos hl]
    takeout_lets; intro_let
    if hx : lt x[i] x[lhs] then
      simp only [if_pos hx]
      exact node_odd_next x i hi hl (Nat.le_of_not_lt hr) hx
    else
      simp only [if_neg hx]
      exact node_odd_end x i hi hl (Nat.le_of_not_lt hr) (Bool.of_not_eq_true hx)
  else
    simp only [dif_neg hr, dif_neg hl]
    exact leaf x i (Nat.le_of_not_lt hl)
termination_by _ => x.size - i
decreasing_by exact _hdecreasing

variable {lt} {x : Subarray α} {i : Nat} {y : Subarray α}

theorem to_eq (h : heapifyDown.OpSpec lt x i y) : y = heapifyDown lt x i := by
  induction h with
  | node_next_left x i y hi hl hr hx' hx _ IH =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_pos hr, if_pos hx', if_pos hx]
    exact IH
  | node_end_left x i hi hl hr hx' hx =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_pos hr, if_pos hx', if_neg (Bool.eq_false_iff.mp hx)]
  | node_next_right x i y hi hl hr hx' hx _ IH =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_pos hr, if_neg (Bool.eq_false_iff.mp hx'), if_pos hx]
    exact IH
  | node_end_right x i hi hl hr hx' hx =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_pos hr, if_neg (Bool.eq_false_iff.mp hx'), if_neg (Bool.eq_false_iff.mp hx)]
  | node_odd_next x i hi hl hr hx =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_neg (Nat.not_lt_of_le hr), dif_pos hl, if_pos hx]
  | node_odd_end x i hi hl hr hx =>
    unfold heapifyDown heapifyDownAux
    simp only [dif_neg (Nat.not_lt_of_le hr), dif_pos hl, if_neg (Bool.eq_false_iff.mp hx)]
  | leaf x i hl =>
    have hr : 2*i+2 ≥ x.size := .step hl
    unfold heapifyDown heapifyDownAux
    simp only [dif_neg (Nat.not_lt_of_le hr), dif_neg (Nat.not_lt_of_le hl)]

theorem size_as_eq (h : heapifyDown.OpSpec lt x i y) : y.as.size = x.as.size := by
  induction h <;> try rfl
  all_goals simp only [Subarray.size_as_swap] at *
  all_goals assumption

theorem start_eq (h : heapifyDown.OpSpec lt x i y) : y.start = x.start := by
  induction h <;> try rfl
  all_goals next IH => simp only [IH, Subarray.start_swap]

theorem stop_eq (h : heapifyDown.OpSpec lt x i y) : y.stop = x.stop := by
  induction h <;> try rfl
  all_goals next IH => simp only [IH, Subarray.stop_swap]

theorem size_eq (h : heapifyDown.OpSpec lt x i y) : y.size = x.size := by
  simp only [Subarray.size, h.stop_eq, h.start_eq]

theorem get_not_descendant (h : heapifyDown.OpSpec lt x i y) (k : Nat) {hk : k < y.size} (hdesc : ¬ Descendant i k) : y[k] = x[k]'(h.size_eq ▸ hk) := by
  induction h <;> try rfl
  case node_next_left x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk fun h => hdesc (Descendant.trans (.child_left i) h)]
    apply Subarray.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact hdesc (.refl _)
    . exact hdesc (.child_left _)
  case node_next_right x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk fun h => hdesc (Descendant.trans (.child_right i) h)]
    apply Subarray.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact hdesc (.refl _)
    . exact hdesc (.child_right _)
  case node_odd_next x i hi hl hr hx =>
    apply Subarray.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact hdesc (.refl _)
    . exact hdesc (.child_left _)

theorem exists_get_descendant (h : heapifyDown.OpSpec lt x i y) (k : Nat) (hk : k < x.size) (hdesc : Descendant i k) : ∃ (l : Nat) (hl : l < x.size), Descendant i l ∧ y[k]'(h.size_eq ▸ hk) = x[l] := by
  induction h <;> try exact ⟨k,hk,hdesc,rfl⟩
  case node_next_left x i y hi hl hr hx' hx h IH =>
    if hdesc' : Descendant (2*i+1) k then
      have ⟨l,hl,hld,IH⟩ := @IH hk hdesc'
      simp only [IH, Subarray.getElem_swap]
      if hll : 2*i+1 = l then
        cases hll; simp only [ite_true]
        exact ⟨i, hi, .refl i, rfl⟩
      else
        rewrite [if_neg hll, if_neg <| Nat.ne_of_lt <| trans (lt_child_left i) hld.le]
        exact ⟨l, hl, .trans (.child_left i) hld, rfl⟩
    else
      simp only [h.get_not_descendant k hdesc', Subarray.getElem_swap]
      rewrite [if_neg (c:=2*i+1=k) fun h => by cases h; exact hdesc' (.refl _)]
      if hik : i = k then
        cases hik; simp only [ite_true]
        exact ⟨2*k+1, hl, .child_left k, rfl⟩
      else
        simp only [if_neg hik]
        exact ⟨k, hk, hdesc, rfl⟩
  case node_next_right x i y hi hl hr hx' hx h IH =>
    if hdesc' : Descendant (2*i+2) k then
      have ⟨l,hl,hld,IH⟩ := @IH hk hdesc'
      simp only [IH, Subarray.getElem_swap]
      if hrl : 2*i+2 = l then
        cases hrl; simp only [ite_true]
        exact ⟨i, hi, .refl i, rfl⟩
      else
        rewrite [if_neg hrl, if_neg <| Nat.ne_of_lt <| trans (lt_child_right i) hld.le]
        exact ⟨l, hl, .trans (.child_right i) hld, rfl⟩
    else
      simp only [h.get_not_descendant k hdesc', Subarray.getElem_swap]
      rewrite [if_neg (c:=2*i+2=k) fun h => by cases h; exact hdesc' (.refl _)]
      if hik : i = k then
        cases hik; simp only [ite_true]
        exact ⟨2*k+2, hr, .child_right k, rfl⟩
      else
        simp only [if_neg hik]
        exact ⟨k, hk, hdesc, rfl⟩
  case node_odd_next x i hi hl hr hx =>
    simp only [Subarray.getElem_swap]
    if hlk : 2*i+1 = k then
      cases hlk; simp only [ite_true]
      exact ⟨i, hi, .refl i, rfl⟩
    else if hik : i = k then
      cases hik; simp only [if_neg hlk, ite_true]
      exact ⟨2*k+1, hl, .child_left k, rfl⟩
    else
      simp only [if_neg hlk, if_neg hik]
      exact ⟨k, hk, hdesc, rfl⟩

theorem exists_get (h : heapifyDown.OpSpec lt x i y) (k : Nat) (hk : k < x.size) : ∃ (l : Nat) (hl : l < x.size), y[k]'(h.size_eq ▸ hk) = x[l] := by
  if hd : Descendant i k then
    have ⟨l, hl, _, hl'⟩ := h.exists_get_descendant k hk hd
    exact ⟨l, hl, hl'⟩
  else
    simp only [h.get_not_descendant k hd]
    exact ⟨k, hk, rfl⟩

theorem get_as_eq_of_lt_start (h : heapifyDown.OpSpec lt x i y) (k : Nat) {hk : k < y.as.size} (hlt : k < x.start) : y.as[k] = x.as[k]'(h.size_as_eq ▸ hk) := by
  induction h <;> try rfl
  case node_next_left x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk hlt]; simp only [x.as_swap]
    apply Array.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right i
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right _
  case node_next_right x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk hlt]; simp only [x.as_swap]
    apply Array.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right i
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right _
  case node_odd_next x i hi hl _ _ =>
    apply Array.getElem_swap_ne <;> (dsimp; intro hik; cases hik)
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right i
    . exact Nat.not_le_of_lt hlt <| x.start.le_add_right _

theorem get_as_eq_of_ge_stop (h : heapifyDown.OpSpec lt x i y) (k : Nat) {hk : k < y.as.size} (hge : k ≥ x.stop) : y.as[k] = x.as[k]'(h.size_as_eq ▸ hk) := by
  induction h <;> try rfl
  case node_next_left x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk hge]
    apply Array.getElem_swap_ne <;> (dsimp; intro h; cases h)
    all_goals exact Nat.not_lt_of_le hge <| x.castIndex_lt_stop _
  case node_next_right x i y hi hl hr hx' hx _ IH =>
    rewrite [@IH hk hge]
    apply Array.getElem_swap_ne <;> (dsimp; intro h; cases h)
    all_goals exact Nat.not_lt_of_le hge <| x.castIndex_lt_stop _
  case node_odd_next x i hi hl _ _ =>
    apply Array.getElem_swap_ne <;> (dsimp; intro h; cases h)
    all_goals exact Nat.not_lt_of_le hge <| x.castIndex_lt_stop _

end heapifyDown.OpSpec


@[simp]
theorem size_as_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).as.size = x.as.size :=
  (heapifyDown.OpSpec.mk lt x i).size_as_eq

@[simp]
theorem start_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).start = x.start :=
  (heapifyDown.OpSpec.mk lt x i).start_eq

@[simp]
theorem stop_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).stop = x.stop :=
  (heapifyDown.OpSpec.mk lt x i).stop_eq

@[simp]
theorem size_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).size = x.size :=
  (heapifyDown.OpSpec.mk lt x i).size_eq

theorem get_as_heapifyDown_of_lt_start (x : Subarray α) (i k : Nat) {hk : k < (heapifyDown lt x i).as.size} (hk' : k < x.start) : (heapifyDown lt x i).as[k] = x.as[k]'(size_as_heapifyDown lt x i ▸ hk) :=
  (heapifyDown.OpSpec.mk lt x i).get_as_eq_of_lt_start k hk'

theorem get_as_heapifyDown_of_ge_stop (x : Subarray α) (i k : Nat) {hk : k < (heapifyDown lt x i).as.size} (hk' : k ≥ x.stop) : (heapifyDown lt x i).as[k] = x.as[k]'(size_as_heapifyDown lt x i ▸ hk) :=
  (heapifyDown.OpSpec.mk lt x i).get_as_eq_of_ge_stop k hk'

theorem get_heapifyDown_not_descendant (x : Subarray α) (i k : Nat) {hk : k < (heapifyDown lt x i).size} (hdesc : ¬ Descendant i k) : (heapifyDown lt x i)[k] = x[k]'(size_heapifyDown lt x _ ▸ hk) :=
  (heapifyDown.OpSpec.mk lt x i).get_not_descendant k hdesc

theorem get_heapifyDown_lt (x : Subarray α) (i : Nat) (k : Nat) {hk : k < (heapifyDown lt x i).size} (hki : k < i) : (heapifyDown lt x i)[k] = x[k]'(trans (α:=Nat) hk (size_heapifyDown lt x i)) := by
  refine get_heapifyDown_not_descendant lt x i k ?_
  intro h
  exact absurd h.le (Nat.not_le_of_gt hki)

theorem exists_get_heapifyDown_descendant (x : Subarray α) (i k : Nat) (hk : k < x.size) (hdesc : Descendant i k) : ∃ (l : Nat) (hl : l < x.size), Descendant i l ∧ (heapifyDown lt x i)[k]'(size_heapifyDown lt x i ▸ hk) = x[l] :=
  (heapifyDown.OpSpec.mk lt x i).exists_get_descendant k hk hdesc

theorem exists_get_heapifyDown (x : Subarray α) (i k : Nat) (hk : k < x.size) : ∃ (l : Nat) (hl : l < x.size), (heapifyDown lt x i)[k]'(size_heapifyDown lt x i ▸ hk) = x[l] :=
  (heapifyDown.OpSpec.mk lt x i).exists_get k hk

/-!
* TODO

```lean
theorem get_heapifyDown_eq (x : Subarray α) (i : Nat) {hi : i < (heapifyDown lt x i).size} :
    (heapifyDown lt x i)[i] =
    have : i < x.size := trans (α:=Nat) (s:=Eq) hi (size_heapifyDown lt x i)
    if hr : 2*i + 2 < x.size then
      if lt x[2*i+2] (x[2*i+1]'(Nat.le_of_succ_le hr)) then
        if lt x[i] (x[2*i+1]'(Nat.le_of_succ_le hr)) then
          x[2*i+1]'(Nat.le_of_succ_le hr)
        else
          x[i]
      else
        if lt x[i] x[2*i+2] then x[2*i+2] else x[i]
    else if hl : 2*i + 1 < x.size then
      if lt x[i] x[2*i+1] then x[2*i+1] else x[i]
    else
      x[i]
    := by
  unfold heapifyDown heapifyDownAux
  takeout_lets; iterate intro_let
  if hr : rhs < x.size then
    simp (config := {zeta:=false,beta:=false}) only [dif_pos hr]
    takeout_lets; iterate intro_let
    if hx' : lt x[rhs] x[lhs] then
      simp (config := {zeta:=false,beta:=false}) only [if_pos hx']
      if hx : lt x[i] x[lhs] then
        simp (config := {zeta:=false,beta:=false}) only [if_pos hx, heapifyDownAux_eq]
        rewrite [get_heapifyDown_lt lt (x.swap ⟨i,hi⟩ ⟨lhs,hl⟩) lhs i (lt_child_left i)]
        rw [x.getElem_swap_left]
      else
        simp only [if_neg hx]
    else
      simp (config := {zeta:=false,beta:=false}) only [if_neg hx']
      if hx : lt x[i] x[rhs] then
        simp (config := {zeta:=false,beta:=false}) only [if_pos hx]
        rewrite [get_heapifyDown_lt lt (x.swap ⟨i,hi⟩ ⟨rhs,hr⟩) rhs i (lt_child_right i)]
        rw [x.getElem_swap_left]
      else
        simp only [if_neg hx]
  else if hl : lhs < x.size then
    simp (config := {zeta:=false,beta:=false}) only [dif_neg hr, dif_pos hl]
    if hx : lt x[i] x[lhs] then
      simp only [if_pos hx]; rw [x.getElem_swap_left]
    else
      simp only [if_neg hx]
  else
    simp only [dif_neg hr, dif_neg hl]
```
-/


/-! ### Declarations about `BinaryHeap.mkHeap` -/

@[inline]
unsafe def mkHeapUnsafeCore (x : Array α) (start size : USize) : Array α :=
  unsafe let rec @[specialize] loop (x : Array α) (n : USize) : Array α :=
    if n == 0 then x else
      let n : USize := n-1
      let x := heapifyDownUnsafeCore lt x start size n
      loop x n
  loop x (size / 2)

/-- Unsafe implementation of `BinaryHeap.mkHeap`. -/
@[inline]
unsafe def mkHeapUnsafe (x : Subarray α) : Subarray α :=
  let ⟨x,start,stop,_,_⟩ := x
  let ustart : USize := start.toUSize
  let usize : USize := stop.toUSize - ustart
  ⟨mkHeapUnsafeCore lt x ustart usize, start, stop, lcProof, lcProof⟩

/--
`BinaryHeap.mkHeap lt x` make `x : Subarray α` into a binary heap with respect to a comparison function `lt : α → α → Bool`.
Note that the definition is equivalent to `Nat.foldRev (fun n x => heapifyDown lt x n) (n.size / 2) x`; see `BinaryHeap.mkHeap_eq_foldRev`.
-/
@[implemented_by mkHeapUnsafe]
def mkHeap (x : Subarray α) : Subarray α :=
  let rec loop (x : Subarray α) : (n : Nat) → Subarray α
  | 0 => x
  | n+1 => loop (heapifyDown lt x n) n
  loop x (x.size / 2)

theorem mkHeap_eq_foldRev (x : Subarray α) : mkHeap lt x = Nat.foldRev (fun n x => heapifyDown lt x n) (x.size / 2) x := by
  unfold mkHeap; generalize x.size/2 = n
  induction n generalizing x with
  | zero => rfl
  | succ n IH => exact IH (heapifyDown lt x n)

@[simp]
theorem size_as_mkHeap_loop (x : Subarray α) (n : Nat) : (mkHeap.loop lt x n).as.size = x.as.size := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH => simp only [mkHeap.loop, IH, size_as_heapifyDown]

@[simp]
theorem start_mkHeap_loop (x : Subarray α) (n : Nat) : (mkHeap.loop lt x n).start = x.start := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH => dsimp [mkHeap.loop]; rw [IH, start_heapifyDown]

@[simp]
theorem stop_mkHeap_loop (x : Subarray α) (n : Nat) : (mkHeap.loop lt x n).stop = x.stop := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH => dsimp [mkHeap.loop]; rw [IH, stop_heapifyDown]

@[simp]
theorem size_mkHeap_loop (x : Subarray α) (n : Nat) : (mkHeap.loop lt x n).size = x.size := by
  dsimp [Subarray.size]; rw [start_mkHeap_loop, stop_mkHeap_loop]

theorem get_as_mkHeap_loop_of_lt_start (x : Subarray α) (n k : Nat) {hk : k < (mkHeap.loop lt x n).as.size} (hlt : k < x.start) : (mkHeap.loop lt x n).as[k] = x.as[k]'(size_as_mkHeap_loop lt x n ▸ hk) := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH =>
    dsimp [mkHeap.loop] at hk ⊢
    conv at hk => rw [size_as_mkHeap_loop, size_as_heapifyDown]
    specialize @IH (heapifyDown lt x n)
      ((size_as_mkHeap_loop lt _ n).symm ▸ size_as_heapifyDown lt x n ▸ hk)
      (start_heapifyDown lt x n ▸ hlt)
    rw [IH, get_as_heapifyDown_of_lt_start lt x n k hlt]

theorem get_as_mkHeap_loop_of_ge_stop (x : Subarray α) (n k : Nat) {hk : k < (mkHeap.loop lt x n).as.size} (hge : k ≥ x.stop) : (mkHeap.loop lt x n).as[k] = x.as[k]'(size_as_mkHeap_loop lt x n ▸ hk) := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH =>
    dsimp [mkHeap.loop] at hk ⊢
    conv at hk => rw [size_as_mkHeap_loop, size_as_heapifyDown]
    specialize @IH (heapifyDown lt x n)
      ((size_as_mkHeap_loop lt _ n).symm ▸ size_as_heapifyDown lt x n ▸ hk)
      (stop_heapifyDown lt x n ▸ hge)
    rw [IH, get_as_heapifyDown_of_ge_stop lt x n k hge]

theorem exists_get_mkHeap_loop (x : Subarray α) (n k : Nat) (hk : k < x.size) : ∃ (l : Nat) (hl : l < x.size), (mkHeap.loop lt x n)[k]'(size_mkHeap_loop lt x n ▸ hk) = x[l] := by
  induction n generalizing x with
  | zero => exact ⟨k,hk,rfl⟩
  | succ n IH =>
    dsimp [mkHeap.loop]
    have ⟨l',hl',IH⟩ := IH (heapifyDown lt x n) (size_heapifyDown lt x n ▸ hk)
    simp only [IH]
    exact exists_get_heapifyDown lt x n l' (size_heapifyDown lt x n ▸ hl')

@[simp]
theorem size_as_mkHeap (x : Subarray α) : (mkHeap lt x).as.size = x.as.size :=
  size_as_mkHeap_loop lt x (x.size/2)

@[simp]
theorem start_mkHeap (x : Subarray α) : (mkHeap lt x).start = x.start :=
  start_mkHeap_loop lt x (x.size/2)

@[simp]
theorem stop_mkHeap (x : Subarray α) : (mkHeap lt x).stop = x.stop :=
  stop_mkHeap_loop lt x (x.size/2)

@[simp]
theorem size_mkHeap (x : Subarray α) : (mkHeap lt x).size = x.size :=
  size_mkHeap_loop lt x (x.size/2)

theorem get_as_mkHeap_of_lt_start (x : Subarray α) (i : Nat) {hi : i < (mkHeap lt x).as.size} (hlt : i < x.start) : (mkHeap lt x).as[i] = x.as[i]'(size_as_mkHeap lt x ▸ hi) :=
  get_as_mkHeap_loop_of_lt_start lt x _ i hlt

theorem get_as_mkHeap_of_ge_stop (x : Subarray α) (i : Nat) {hi : i < (mkHeap lt x).as.size} (hge : i ≥ x.stop) : (mkHeap lt x).as[i] = x.as[i]'(size_as_mkHeap lt x ▸ hi) :=
  get_as_mkHeap_loop_of_ge_stop lt x _ i hge

theorem exists_get_mkHeap (x : Subarray α) (i : Nat) (hi : i < x.size) : ∃ (k : Nat) (hk : k < x.size), (mkHeap lt x)[i]'(size_mkHeap lt x ▸ hi) = x[k] :=
  exists_get_mkHeap_loop lt x (x.size/2) i hi


/-! ### Declaration about `popMax` -/

/--
Pop the top element out of a heap.
The popped element is, if any, moved to the tail of the subarray.
Indeed,

* if `x.start == x.stop`, then `BinaryHeap.popMax lt x = x`;
* if `x.start < x.stop`, then the following holds:
  - `(BinaryHeap.popMax lt x).start = x.start`
  - `(BinaryHeap.popMax lt x).stop = x.stop - 1`
  - `(BinaryHeap.popMax lt x).as[x.stop - 1] = x[0]`
  - `BinaryHeap.popMax lt x` is a heap with respect to `lt` provided so is `x`.
-/
def popMax (x : Subarray α) : Subarray α :=
  if h : x.start < x.stop then
    have : 0 < x.size := Nat.sub_pos_of_lt h
    let x := x.swap ⟨0, this⟩ ⟨x.size-1, Nat.pred_lt' this⟩
    heapifyDown lt (x.shrinkOne' h) 0
  else
    x

theorem popMax_empty (x : Subarray α) (h : x.start = x.stop) : popMax lt x = x :=
  dif_neg (c:=x.start < x.stop) <| Nat.not_lt_of_le <| h ▸ .refl

@[simp]
theorem size_as_popMax (x : Subarray α) : (popMax lt x).as.size = x.as.size := by
  delta popMax
  if h : x.start < x.stop then
    simp only [dif_pos h, size_as_heapifyDown, Subarray.size_as_shrinkOne', Subarray.size_as_swap]
  else
    simp only [dif_neg h]

@[simp]
theorem start_popMax (x : Subarray α) : (popMax lt x).start = x.start := by
  delta popMax
  if h : x.start < x.stop then
    simp only [dif_pos h, start_heapifyDown, Subarray.start_shrinkOne', Subarray.start_swap]
  else
    simp only [dif_neg h]

@[simp]
theorem stop_popMax_le_stop (x : Subarray α) : (popMax lt x).stop ≤ x.stop := by
  delta popMax
  if h : x.start < x.stop then
    simp only [dif_pos h, stop_heapifyDown, Subarray.stop_shrinkOne', Subarray.stop_swap]
    exact x.stop.pred_le
  else
    simp only [dif_neg h]; exact .refl

@[simp]
theorem size_popMax (x : Subarray α) : (popMax lt x).size = x.size - 1 := by
  delta popMax
  cases Nat.lt_or_eq_of_le x.h₁ with
  | inl hlt =>
    simp only [dif_pos hlt, size_heapifyDown, Subarray.size_shrinkOne', Subarray.size_swap]
  | inr heq =>
    rewrite [dif_neg (c:=x.start < x.stop) (heq ▸ x.start.lt_irrefl)]
    simp only [Subarray.size, heq, x.stop.sub_self]

@[simp]
theorem stop_popMax (x : Subarray α) (h : x.start < x.stop) : (popMax lt x).stop = x.stop - 1 := by
  delta popMax
  simp only [dif_pos h, stop_heapifyDown]
  refine Eq.trans (Subarray.stop_shrinkOne' _ ?_) ?_
  all_goals simp only [Subarray.stop_swap, Subarray.start_swap]
  exact h

theorem get_as_popMax_of_lt_start (x : Subarray α) (i : Nat) {hi : i < (popMax lt x).as.size} (hlt : i < x.start) : (popMax lt x).as[i] = x.as[i]'(trans hlt x.start_le :) := by
  delta popMax
  if h : x.start < x.stop then
    simp only [dif_pos h]
    rewrite [get_as_heapifyDown_of_lt_start lt _ 0 i]
    all_goals simp only [Subarray.as_shrinkOne', Subarray.as_swap, Subarray.start_shrinkOne', Subarray.start_swap]
    . refine Array.getElem_swap_ne x.as _ _ _ (Nat.ne_of_gt hlt) ?_
      exact Nat.ne_of_gt <| trans hlt (x.castIndex_ge_start _)
    . exact hlt
  else
    simp only [dif_neg h]

theorem get_as_popMax_of_ge_stop (x : Subarray α) (i : Nat) {hi : i < (popMax lt x).as.size} (hge : i ≥ x.stop) : (popMax lt x).as[i] = x.as[i]'(size_as_popMax lt x ▸ hi) := by
  delta popMax
  if h : x.start < x.stop then
    simp only [dif_pos h]
    rewrite [get_as_heapifyDown_of_ge_stop lt _ 0 i]
    . simp only [Subarray.as_shrinkOne']
      refine Array.getElem_swap_ne x.as _ _ _ ?_ ?_
      . exact Nat.ne_of_lt <| trans (x.castIndex_lt_stop _) hge
      . exact Nat.ne_of_lt <| trans (x.castIndex_lt_stop _) hge
    . simp only [Subarray.stop_shrinkOne']
      exact Nat.le_trans x.stop.pred_le hge
  else
    simp only [dif_neg h]

theorem get_as_popMax_stop_sub_one (x : Subarray α) (hs : x.start < x.stop) : (popMax lt x).as[x.stop-1]'(size_as_popMax lt x ▸ trans (x.stop.pred_lt' hs) x.h₂) = x[0]'(Nat.sub_pos_of_lt hs) := by
  delta popMax
  simp only [dif_pos hs]
  rewrite [get_as_heapifyDown_of_ge_stop lt _ 0 (x.stop-1)]
  . simp only [Subarray.as_shrinkOne', Subarray.as_swap]
    simp only [Array.getElem_swap, Subarray.castIndex]
    rw [if_pos]; rfl
    rewrite [Subarray.size, ← Nat.add_sub_assoc (Nat.sub_pos_of_lt hs), Nat.add_sub_cancel' x.h₁]
    rfl
  . simp only [Subarray.stop_shrinkOne', Subarray.stop_swap]
    exact .refl

theorem exists_get_popMax (x : Subarray α) (i : Nat) (hi : i < x.size - 1) : ∃ (k : Nat) (hk : k < x.size), 0 < k ∧ (popMax lt x)[i]'(size_popMax lt x ▸ hi) = x[k] := by
  delta popMax; dsimp
  have : i + 1 < x.stop - x.start := Nat.add_lt_of_lt_sub hi
  have : x.start < x.stop := calc
    x.start < i+1+x.start := Nat.lt_add_of_pos_left i.zero_lt_succ
    _       < x.stop := Nat.add_lt_of_lt_sub this
  simp only [dif_pos this]
  have hzero : 0 < x.size := Nat.sub_pos_of_lt this
  have hlast : x.size-1 < x.size := Nat.pred_lt' <| Nat.add_lt_of_lt_sub hi
  have ⟨k,hk,h⟩ :=
    exists_get_heapifyDown lt ((x.swap ⟨0,hzero⟩ ⟨x.size-1,hlast⟩).shrinkOne' this) 0 i <| by
      simp only [Subarray.size_shrinkOne', Subarray.size_swap]
      exact hi
  simp only [h, Subarray.getElem_shrinkOne', Subarray.getElem_swap]; clear h
  conv at hk => simp only [Subarray.size_shrinkOne', Subarray.size_swap]
  simp only [if_neg (Nat.ne_of_gt hk)]
  if hzk : 0 = k then
    simp only [if_pos hzk]
    exists x.size-1, hlast
    exact ⟨Nat.lt_of_le_of_lt k.zero_le hk, rfl⟩
  else
    simp only [if_neg hzk]
    exists k, (Nat.lt_of_lt_of_le hk x.size.pred_le)
    exact ⟨Nat.pos_of_ne_zero (Ne.symm hzk), rfl⟩


/-! ### Declaration about `heapSort` -/

@[inline]
unsafe def heapSortUnsafeCore (x : Array α) (start size : USize) : Array α :=
  unsafe let rec @[specialize] loop (x : Array α) (n : USize) : Array α :=
    if n == 0 then x else
      -- Equivalent to matching `n` in the expression `n+1`
      let n : USize := n-1
      -- The following two lines are equivalent to `popMax lt x`
      let x := x.uswap start (start + n) lcProof lcProof
      let x := heapifyDownUnsafeCore lt x start n 0
      -- Make sure this is a tail-recursion
      loop x n
  let x := mkHeapUnsafeCore lt x start size
  loop x size

@[inline]
unsafe def heapSortUnsafe (x : Subarray α) : Array α :=
  match x with
  | .mk x start stop _ _ =>
    let ustart : USize := start.toUSize
    let usize : USize := stop.toUSize - ustart
    heapSortUnsafeCore lt x ustart usize

@[implemented_by heapSortUnsafe]
def heapSort (x : Subarray α) : Array α :=
  let rec loop : Subarray α → Nat → Array α
  | x, 0 => x.as
  | x, n+1 => loop (popMax lt x) n
  let x := mkHeap lt x
  loop x x.size

/-- Semantic specification for `heapSort.loop`. -/
protected inductive heapSort.loop.OpSpec : Subarray α → Nat → Array α → Prop where
| zero (x : Subarray α) : loop.OpSpec x 0 x.as
| succ {x : Subarray α} {n : Nat} {y : Array α} : loop.OpSpec (popMax lt x) n y → loop.OpSpec x (n+1) y

namespace heapSort.loop.OpSpec

protected theorem mk (x : Subarray α) (n : Nat) : loop.OpSpec lt x n (heapSort.loop lt x n) := by
  induction n generalizing x with
  | zero => exact .zero x
  | succ n IH => exact .succ <| IH (popMax lt x)

variable {lt} {x : Subarray α} {n : Nat} {y : Array α}

theorem to_eq (h : loop.OpSpec lt x n y) : y = heapSort.loop lt x n := by
  induction h with
  | zero => rfl
  | succ h IH => rw [IH]; rfl

theorem size_eq (h : loop.OpSpec lt x n y) : y.size = x.as.size := by
  induction h with
  | zero => rfl
  | succ h IH => rw [IH, size_as_popMax]

theorem get_eq_of_lt_start (h : loop.OpSpec lt x n y) (i : Nat) {hi : i < y.size} (hlt : i < x.start) : y[i] = x.as[i]'(h.size_eq ▸ hi) := by
  induction h with
  | zero => rfl
  | @succ x n y h IH =>
    specialize @IH hi <| start_popMax lt x ▸ hlt
    exact Eq.trans IH <| get_as_popMax_of_lt_start lt x i hlt

theorem get_eq_of_ge_stop (h : loop.OpSpec lt x n y) (i : Nat) {hi : i < y.size} (hge : i ≥ x.stop) : y[i] = x.as[i]'(h.size_eq ▸ hi) := by
  induction h with
  | zero => rfl
  | @succ x n y h IH =>
    specialize @IH hi <| Nat.le_trans (stop_popMax_le_stop lt x) hge
    exact Eq.trans IH <| get_as_popMax_of_ge_stop lt x i hge

theorem exists_get (h : loop.OpSpec lt x n y) (i : Nat) (ge_start : x.start ≤ i) (lt_stop : i < x.stop) : ∃ (k : Nat) (hk : k < x.size), y[i]'(h.size_eq ▸ trans lt_stop x.h₂) = x[k] := by
  induction h with
  | @zero x =>
    let k := i - x.start
    have hki : i = x.start + k := by
      rw [Nat.add_comm, Nat.sub_add_cancel ge_start]
    have hk : k < x.size := by
      refine Nat.lt_sub_of_add_lt ?_
      simp only [Nat.sub_add_cancel ge_start]
      exact lt_stop
    exists k, hk
    exact getElem_eq (x:=x.as) (y:=x.as) rfl hki
  | @succ x n y h IH =>
    specialize IH (start_popMax lt x ▸ ge_start)
    have hrng : x.start < x.stop := trans ge_start lt_stop
    cases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt lt_stop) with
    | inl hlt =>
      have ⟨k,hk,hy⟩ := IH (stop_popMax lt x hrng ▸ hlt)
      have ⟨l,hl,_,hx⟩ := exists_get_popMax lt x k (size_popMax lt x ▸ hk)
      simp only [hy, hx]
      exact ⟨l, hl, rfl⟩
    | inr heq =>
      cases heq
      rewrite [h.get_eq_of_ge_stop (x.stop-1) (stop_popMax lt x hrng ▸ .refl)]
      rewrite [get_as_popMax_stop_sub_one lt x hrng]
      exact ⟨0, Nat.zero_lt_sub_of_lt hrng, rfl⟩

end heapSort.loop.OpSpec

@[simp]
theorem size_heapSort (x : Subarray α) : (heapSort lt x).size = x.as.size :=
  (heapSort.loop.OpSpec.mk lt _ _).size_eq.trans <|
    size_as_mkHeap lt x

theorem get_heapSort_of_lt_start (x : Subarray α) (i : Nat) {hi : i < (heapSort lt x).size} (hlt : i < x.start) : (heapSort lt x)[i] = x.as[i]'(size_heapSort lt x ▸ hi) :=
  ((heapSort.loop.OpSpec.mk lt (mkHeap lt x) _).get_eq_of_lt_start i (start_mkHeap lt x ▸ hlt)).trans <|
    get_as_mkHeap_of_lt_start lt x i hlt

theorem get_heapSort_of_ge_stop (x : Subarray α) (i : Nat) {hi : i < (heapSort lt x).size} (hge : i ≥ x.stop) : (heapSort lt x)[i] = x.as[i]'(size_heapSort lt x ▸ hi) :=
  ((heapSort.loop.OpSpec.mk lt (mkHeap lt x) _).get_eq_of_ge_stop i (stop_mkHeap lt x ▸ hge)).trans <|
    get_as_mkHeap_of_ge_stop lt x i hge

theorem exists_get_heapSort (x : Subarray α) (i : Nat) (ge_start : x.start ≤ i) (lt_stop : i < x.stop) : ∃ (k : Nat) (hk : k < x.size), (heapSort lt x)[i]'(size_heapSort lt x ▸ trans lt_stop x.h₂) = x[k] :=
  have ⟨k,hk,h₁⟩ :=
    (heapSort.loop.OpSpec.mk lt (mkHeap lt x) (mkHeap lt x).size).exists_get i
      (start_mkHeap lt x ▸ ge_start)
      (stop_mkHeap lt x ▸ lt_stop)
  have ⟨l,hl,h₂⟩ :=
    exists_get_mkHeap lt x k (size_mkHeap lt x ▸ hk)
  ⟨l, hl, h₁.trans h₂⟩

end Algdata.BinaryHeap
