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

theorem size_le_size_as (x : Subarray α) : x.size ≤ x.as.size :=
  Nat.le_trans (x.stop.sub_le x.start) x.h₂

def castIndex (x : Subarray α) (i : Fin x.size) : Fin x.as.size :=
  .mk (x.start + i.1) <| by
    rcases i with ⟨i,hi⟩
    have := Nat.add_lt_of_lt_sub hi
    exact Nat.lt_of_lt_of_le (i.add_comm _ ▸ this) x.h₂

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

theorem swap_comm (x : Subarray α) (i j : Fin x.size) : x.swap i j = x.swap j i := by
  simp [swap]; exact x.as.swap_comm _ _

end Subarray
