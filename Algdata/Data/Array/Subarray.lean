/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Fin.Basic
import Std.Data.Array.Lemmas

import Algdata.Data.Array.Lemmas


/-!
# Auxiliary lemmas about `Subarray`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u

namespace Subarray

variable {α : Type u}


/-! ### Lemmas about indices -/

theorem size_le_size_as (x : Subarray α) : x.size ≤ x.as.size :=
  Nat.le_trans (x.stop.sub_le x.start) x.h₂

/-- Convert an index of `x : Subarray α` to that of the underlying array `x.as : Array α`. -/
@[inline]
def castIndex (x : Subarray α) (i : Fin x.size) : Fin x.as.size :=
  .mk (x.start + i.1) <| by
    rcases i with ⟨i,hi⟩
    have := Nat.add_lt_of_lt_sub hi
    exact Nat.lt_of_lt_of_le (i.add_comm _ ▸ this) x.h₂


/-! ### Declarations about `Subarray.swap` -/

@[inline]
def swap (x : Subarray α) (i j : Fin x.size) : Subarray α := {
  x with
  as :=
    x.as.swap (x.castIndex i) (x.castIndex j)
  h₂ := (x.as.size_swap _ _).symm ▸ x.h₂
}

@[simp]
theorem size_swap (x : Subarray α) (i j : Fin x.size) : (x.swap i j).size = x.size :=
  rfl

theorem getElem_swap (x : Subarray α) (i j : Fin x.size) (k : Nat) {hk : k < (x.swap i j).size} : (x.swap i j)[k] = if j.1 = k then x[i.1] else if i.1 = k then x[j.1] else x[k] := by
  dsimp [swap, getElem]; dsimp [get]
  simp only [Array.getElem_swap, castIndex, Nat.add_left_cancel_iff]

@[simp]
theorem getElem_swap_left (x : Subarray α) (i j : Fin x.size) : (x.swap i j)[i.1] = x[j.1] := by
  rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
  rewrite [getElem_swap]
  dsimp at *
  if hji : j = i then
    cases hji; simp only [ite_true]
  else
    rw [if_neg hji, if_pos rfl]

@[simp]
theorem getElem_swap_right (x : Subarray α) (i j : Fin x.size) : (x.swap i j)[j.1] = x[i.1] := by
  rewrite [getElem_swap]
  rw [if_pos rfl]

theorem getElem_swap_ne (x : Subarray α) (i j : Fin x.size) (k : Nat) {hk : k < (x.swap i j).size} (hik : i.1 ≠ k) (hjk : j.1 ≠ k) : (x.swap i j)[k] = x[k] := by
  rw [getElem_swap, if_neg hjk, if_neg hik]

theorem swap_comm (x : Subarray α) (i j : Fin x.size) : x.swap i j = x.swap j i := by
  simp [swap]; exact x.as.swap_comm _ _


/-! ### Declarations about `Subarray.shrinkOne` -/

/-- Shrink the end of the range of a given subarray `x : Subarray α` by one with the proof that the range is nonempty; see also `Subarray.shrinkOne`. -/
@[inline]
def shrinkOne' (x : Subarray α) (h : x.start < x.stop) : Subarray α :=
  {x with
    stop := x.stop - 1
    h₁ := Nat.le_sub_of_add_le h
    h₂ := Nat.le_trans x.stop.pred_le x.h₂
  }

/-- Shrink the end of the range of a given subarray `x : Subarray α` by one if the range is nonempty; see also `Subarray.shrinkOne'` for the case where `x.start < x.stop` is known. -/
@[inline]
def shrinkOne (x : Subarray α) : Subarray α :=
  if h : x.start < x.stop then
    shrinkOne' x h
  else
    x

@[simp]
theorem as_shrinkOne' (x : Subarray α) (h : x.start < x.stop) : (x.shrinkOne' h).as = x.as :=
  rfl

@[simp]
theorem start_shrinkOne' (x : Subarray α) (h : x.start < x.stop) : (x.shrinkOne' h).start = x.start :=
  rfl

@[simp]
theorem stop_shrinkOne' (x : Subarray α) (h : x.start < x.stop) : (x.shrinkOne' h).stop = x.stop - 1 :=
  rfl

@[simp]
theorem size_shrinkOne' (x : Subarray α) (h : x.start < x.stop) : (x.shrinkOne' h).size = x.size - 1 :=
  show x.stop - 1 - x.start = (x.stop - x.start) - 1 by
  simp only [Nat.sub_sub, Nat.add_comm 1 x.start]

end Subarray
