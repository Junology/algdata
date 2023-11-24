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

@[simp]
private theorem heapifyDownAux_eq (x : Subarray α) (i : Nat) : heapifyDownAux lt x i = heapifyDown lt x i :=
  rfl

@[simp]
theorem size_as_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).as.size = x.as.size := by
  unfold heapifyDown heapifyDownAux
  takeout_lets; iterate intro_let
  if hr : rhs < x.size then
    rewrite [dif_pos hr]
    takeout_lets; iterate intro_let
    if hx : lt x[i] (x[j]'hj.2) then
      rewrite [if_pos hx]
      have := ‹x.size - j < x.size - i›
      have IH := size_as_heapifyDown (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j
      rewrite [IH]
      simp only [Subarray.swap, Array.size_swap]
    else
      rw [if_neg hx]
  else if hl : lhs < x.size then
    rewrite [dif_neg hr, dif_pos hl]
    takeout_lets; intro_let
    if hx : lt x[i] x[lhs] then
      rewrite [if_pos hx]
      simp only [Subarray.swap, Array.size_swap]
    else
      rw [if_neg hx]
  else
    rw [dif_neg hr, dif_neg hl]
termination_by _ => x.size - i

@[simp]
theorem start_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).start = x.start := by
  unfold heapifyDown heapifyDownAux
  takeout_lets; intro lhs rhs
  if hr : rhs < x.size then
    rewrite [dif_pos hr]
    takeout_lets; iterate intro_let
    if hx : lt x[i] (x[j]'hj.2) then
      rewrite [if_pos hx]
      have := ‹x.size - j < x.size - i›
      exact start_heapifyDown (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j
    else
      rw [if_neg hx]
  else if hl : lhs < x.size then
    rewrite [dif_neg hr, dif_pos hl]
    takeout_lets; intro_let
    if hx : lt x[i] x[lhs] then
      rewrite [if_pos hx]; rfl
    else
      rw [if_neg hx]
  else
    rw [dif_neg hr, dif_neg hl]
termination_by _ => x.size - i

@[simp]
theorem stop_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).stop = x.stop := by
  unfold heapifyDown heapifyDownAux
  takeout_lets; intro lhs rhs
  if hr : rhs < x.size then
    rewrite [dif_pos hr]
    takeout_lets; iterate intro_let
    if hx : lt x[i] (x[j]'hj.2) then
      rewrite [if_pos hx]
      have := ‹x.size - j < x.size - i›
      exact stop_heapifyDown (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j
    else
      rw [if_neg hx]
  else if hl : lhs < x.size then
    rewrite [dif_neg hr, dif_pos hl]
    takeout_lets; intro_let
    if hx : lt x[i] x[lhs] then
      rewrite [if_pos hx]; rfl
    else
      rw [if_neg hx]
  else
    rw [dif_neg hr, dif_neg hl]
termination_by _ => x.size - i

@[simp]
theorem size_heapifyDown (x : Subarray α) (i : Nat) : (heapifyDown lt x i).size = x.size := by
  unfold Subarray.size
  rw [start_heapifyDown, stop_heapifyDown]


theorem get_heapifyDown_not_descendant (x : Subarray α) (i : Nat) (k : Nat) {hk : k < (heapifyDown lt x i).size} (hdesc : ¬ Descendant i k) : (heapifyDown lt x i)[k] = x[k]'(size_heapifyDown lt x _ ▸ hk) := by
  have hk' : k < x.size := by
    rewrite [size_heapifyDown] at hk; exact hk
  have hkne : i ≠ k := fun h => by
    cases h; exact hdesc (.refl i)
  unfold heapifyDown heapifyDownAux
  takeout_lets; iterate intro_let
  if hr : rhs < x.size then
    simp (config:={zeta:=false,beta:=false}) only [dif_pos hr]
    takeout_lets; iterate intro_let
    if hx : lt x[i] (x[j]'hj.2) then
      simp (config:={zeta:=false}) [if_pos hx]
      have hdescj : Descendant i j := by
        if hxj : lt (x[rhs]'hr) (x[lhs]'hl) then
          dsimp at hxj ⊢; rewrite [if_pos hxj]; exact .child_left _
        else
          dsimp at hxj ⊢; rewrite [if_neg hxj]; exact .child_right _
      have : (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩)[k]'hk' = x[k]'hk' := by
        simp (config := {zeta:=false}) only [x.getElem_swap]
        rw [if_neg (?_ : j ≠ k), if_neg hkne]
        intro h; rewrite [← h] at hdesc; exact hdesc hdescj
      rewrite [← this]
      have _hterm := ‹x.size - j < x.size - i›
      exact get_heapifyDown_not_descendant (x.swap ⟨i,hi⟩ ⟨j,hj.2⟩) j k (hdescj.irrel_descend hdesc)
    else
      simp only [if_neg hx]
  else if hl : lhs < x.size then
    simp (config:={zeta:=false}) only [dif_neg hr, dif_pos hl]
    have hi : i < x.size := trans (lt_child_left i) hl
    if hx : lt x[i] x[lhs] then
      simp (config:={zeta:=false}) only [if_pos hx, x.getElem_swap]
      rw [if_neg (?_ : lhs ≠ k), if_neg hkne]
      intro h; rewrite [← h] at hdesc
      exact hdesc <| .child_left i
    else
      simp only [if_neg hx]
  else
    simp only [dif_neg hr, dif_neg hl]
termination_by _ => x.size - i
decreasing_by exact _hterm

theorem get_heapifyDown_lt (x : Subarray α) (i : Nat) (k : Nat) {hk : k < (heapifyDown lt x i).size} (hki : k < i) : (heapifyDown lt x i)[k] = x[k]'(trans (α:=Nat) hk (size_heapifyDown lt x i)) := by
  refine get_heapifyDown_not_descendant lt x i k ?_
  intro h
  exact absurd h.le (Nat.not_le_of_gt hki)

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

theorem exists_get_heapifyDown_eq (x : Subarray α) (i : Fin x.size) : ∃ (k : Fin x.size), Descendant i.1 k.1 ∧ (heapifyDown lt x i.1)[i.1] = x[k.1] := by
  simp only [get_heapifyDown_eq]
  if hr : 2*i.1+2 < x.size then
    if hx : lt x[2*i.1+2] (x[2*i.1+1]'(Nat.lt_of_succ_lt hr)) then
      if hx' : lt x[i.1] (x[2*i.1+1]'(Nat.lt_of_succ_lt hr)) then
        rewrite [dif_pos hr, if_pos hx, if_pos hx']
        exact ⟨⟨2*i.1+1, Nat.lt_of_succ_lt hr⟩, .child_left i.1, rfl⟩
      else
        rewrite [dif_pos hr, if_pos hx, if_neg hx']
        exact ⟨i, .refl i.1, rfl⟩
    else
      if hx' : lt x[i.1] x[2*i.1+2] then
        rewrite [dif_pos hr, if_neg hx, if_pos hx']
        exact ⟨⟨2*i.1+2, hr⟩, .child_right i.1, rfl⟩
      else
        rewrite [dif_pos hr, if_neg hx, if_neg hx']
        exact ⟨i, .refl i.1, rfl⟩
  else if hl : 2*i+1 < x.size then
    if hx : lt x[i.1] x[2*i.1+1] then
      rewrite [dif_neg hr, dif_pos hl, if_pos hx]
      exact ⟨⟨2*i.1+1, hl⟩, .child_left i.1, rfl⟩
    else
      rewrite [dif_neg hr, dif_pos hl, if_neg hx]
      exact ⟨i, .refl i.1, rfl⟩
  else
    rewrite [dif_neg hr, dif_neg hl]
    exact ⟨i, .refl i.1, rfl⟩

#eval heapifyDown (fun i j => decide (i < j)) #[3,1,4,1,5,9,2].toSubarray 0
#print axioms heapifyDown
#print axioms start_heapifyDown
#print axioms stop_heapifyDown
#print axioms size_heapifyDown


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

/-- `BinaryHeap.mkHeap lt x` make `x : Subarray α` into a binary heap with respect to a comparison function `lt : α → α → Bool`. -/
@[implemented_by mkHeapUnsafe]
def mkHeap (x : Subarray α) : Subarray α :=
  let rec loop (x : Subarray α) : (n : Nat) → Subarray α
  | 0 => x
  | n+1 => loop (heapifyDown lt x n) n
  loop x (x.size / 2)

@[simp]
theorem size_as_mkHeap (x : Subarray α) : (mkHeap lt x).as.size = x.as.size := by
  suffices ∀ (x : Subarray α) (n : Nat), (mkHeap.loop lt x n).as.size = x.as.size
    from this x _
  clear x; intro x n
  induction n generalizing x with
  | zero => rfl
  | succ n IH => simp only [mkHeap.loop, IH, size_as_heapifyDown]

@[simp]
theorem start_mkHeap (x : Subarray α) : (mkHeap lt x).start = x.start := by
  suffices ∀ (x : Subarray α) (n : Nat), (mkHeap.loop lt x n).start = x.start
    from this x _
  clear x; intro x n
  induction n generalizing x with
  | zero => rfl
  | succ n IH => dsimp [mkHeap.loop]; rw [IH, start_heapifyDown]

@[simp]
theorem stop_mkHeap (x : Subarray α) : (mkHeap lt x).stop = x.stop := by
  suffices ∀ (x : Subarray α) (n : Nat), (mkHeap.loop lt x n).stop = x.stop
    from this x _
  clear x; intro x n
  induction n generalizing x with
  | zero => rfl
  | succ n IH => dsimp [mkHeap.loop]; rw [IH, stop_heapifyDown]

@[simp]
theorem size_mkHeap (x : Subarray α) : (mkHeap lt x).size = x.size := by
  unfold Subarray.size; rw [start_mkHeap, stop_mkHeap]


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
    let stop' := x.stop - 1
    0 |> heapifyDown lt {
      x with
      as := x.as.swap ⟨x.start, trans h x.h₂⟩ ⟨stop', trans (Nat.pred_lt' h) x.h₂⟩
      stop := stop'
      h₁ := Nat.le_pred_of_lt h
      h₂ := by rewrite [Array.size_swap]; exact trans x.stop.pred_le x.h₂
    }
  else
    x

@[simp]
theorem size_as_popMax (x : Subarray α) : (popMax lt x).as.size = x.as.size := by
  unfold popMax
  if h : x.start < x.stop then
    simp only [dif_pos h, size_as_heapifyDown, Array.size_swap]
  else
    simp only [dif_neg h]


/-! ### Declaration about `heapSort` -/

@[inline]
unsafe def heapSortUnsafeCore (x : Array α) (start size : USize) : Array α :=
  unsafe let rec @[specialize] loop (x : Array α) (n : USize) : Array α :=
    if n == 0 then x else
      let n : USize := n-1
      let x := x.uswap start (start + n) lcProof lcProof
      let x := heapifyDownUnsafeCore lt x start n 0
      loop x n
  let x := mkHeapUnsafeCore lt x start size
  loop x size

@[inline]
unsafe def heapSortUnsafe (x : Subarray α) : Subarray α :=
  match x with
  | .mk x start stop _ _ =>
    let ustart : USize := start.toUSize
    let usize : USize := stop.toUSize - ustart
    ⟨heapSortUnsafeCore lt x ustart usize, start, stop, lcProof, lcProof⟩

@[implemented_by heapSortUnsafe]
def heapSort (x : Subarray α) : Subarray α :=
  let rec loop : Nat → (x : Subarray α) → {y : Array α // y.size = x.as.size}
  | 0, x => ⟨x.as, rfl⟩
  | n+1, x =>
    match loop n (popMax lt x) with
    | .mk y h => ⟨y, Eq.trans h <| size_as_popMax lt x⟩
  let x := mkHeap lt x
  {
    x with
    as := (loop x.size x).1
    h₂ := trans (α:=Nat) x.h₂ (loop x.size x).2.symm
  }

@[simp]
theorem size_as_heapSort (x : Subarray α) : (heapSort lt x).as.size = x.as.size := by
  dsimp [heapSort]
  rewrite [(heapSort.loop lt (mkHeap lt x).size (mkHeap lt x)).2]
  exact size_as_mkHeap lt x

@[simp]
theorem start_heapSort (x : Subarray α) : (heapSort lt x).start = x.start :=
  show (mkHeap lt x).start = x.start from start_mkHeap lt x

@[simp]
theorem stop_heapSort (x : Subarray α) : (heapSort lt x).stop = x.stop :=
  show (mkHeap lt x).stop = x.stop from stop_mkHeap lt x

end Algdata.BinaryHeap
