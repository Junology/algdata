/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Nat

/-!
# A variety of recursions on `Nat`
-/

universe u

namespace Nat

/-!
## Complete induction

Given a predicate `p : Nat → Prop`, one can conclude `∀ n, p n` provided `∀ n, (∀ k, k < n → p k) → p n`.
-/

/-- Complete induction using well-founded recursion -/
@[inline]
def recCompleteWF {motive : Nat → Sort u} (ind : (n : Nat) → (∀ (k : Nat), k < n → motive k) → motive n) (n : Nat) : motive n :=
  ind n (λ k _ => recCompleteWF ind k)

/-- Complete induction without well-founded recursion -/
@[implemented_by recCompleteWF]
def recComplete {motive : Nat → Sort u} (ind : (n : Nat) → (∀ (k : Nat), k < n → motive k) → motive n) (n : Nat) : motive n :=
  let rec aux : (n k : Nat) → k ≤ n → motive k
  | 0, k, hk =>
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    ind k (λ l hl => absurd (this ▸ hl) l.not_lt_zero)
  | _+1, 0, _ => ind 0 (λ k hk => absurd hk k.not_lt_zero)
  | n+1, k+1, hk =>
    ind (k+1) (λ l hl => aux n l (Nat.le_of_lt_succ $ Trans.trans hl hk))
  aux n n n.le_refl

/-- Proof that the two implememtations of the complete induction are equivalent. -/
theorem recComplete_eq {motive : Nat → Sort u} {ind : (n : Nat) → (∀ (k : Nat), k < n → motive k) → motive n} {n : Nat} : recComplete (motive:=motive) ind n = recCompleteWF (motive:=motive) ind n := by
  suffices ∀ k (hk : k ≤ n), recComplete.aux (motive:=motive) ind n k hk = recCompleteWF (motive:=motive) ind k
    from this n n.le_refl
  intro k hk
  induction n generalizing k
  case zero =>
    dsimp [recComplete.aux]; unfold recCompleteWF
    have : k = 0 := k.eq_zero_of_le_zero hk
    cases this
    apply congrArg; funext k hk; cases hk
  case succ n h_ind =>
    cases k
    case zero =>
      dsimp [recComplete.aux]; unfold recCompleteWF
      apply congrArg; funext k hk; cases hk
    case succ k =>
      dsimp [recComplete.aux]; unfold recCompleteWF
      apply congrArg; funext k hk; rw [h_ind]
  

/-!
## Ascending recursion with upper bound. -/

def recAscend {motive : Nat → Sort u} {n : Nat} (ceil : motive n) (ascend : ∀ (k : Nat), k < n → motive k.succ → motive k) (k : Nat) (h : k ≤ n) : motive k :=
  if hlt : k < n
    then ascend k hlt (recAscend ceil ascend k.succ (Nat.succ_le_of_lt hlt))
    else
      have : k = n := Nat.le_antisymm h (Nat.le_of_not_lt hlt)
      this ▸ ceil
termination_by _ => n-k


/-!
### Recursion on base2 digits
-/

theorem recBase2_terminates (n : Nat) : n/2 + 1 < n+2 :=
  calc
    n/2 + 1 < (n/2 + 1) + (n/2 + 1) := Nat.lt_add_succ _ _
    _       = (n/2 + 1)*2 := (Nat.mul_two (n/2 + 1)).symm
    _       = (n/2)*2 + 2 := Nat.succ_mul (n/2) 2
    _       ≤ n + 2 := Nat.add_le_add_right (Nat.div_mul_le_self n 2) 2

def recBase2 {motive : Nat → Sort u} (zero : motive 0) (one : motive 1) (next0 : (n : Nat) → motive n.succ → motive (2*n.succ)) (next1 : (n : Nat) → motive n.succ → motive (2*n.succ + 1)) : (n : Nat) → motive n
| 0 => zero
| 1 => one
| n+2 =>
  have hn := calc
    n+2 = 2*((n+2)/2) + (n+2)%2 := (Nat.div_add_mod (n+2) 2).symm
    _   = 2*((n+2)/2) + n%2 := by rw [Nat.add_mod_right n 2]
    _   = 2*(n/2 + 1) + n%2 := by rw [Nat.add_div_right n (Nat.zero_lt_succ 1)]
  if h : n % 2 = 0
  then
    have : n+2 = 2*(n/2 + 1) := by rw [h, Nat.add_zero] at hn; exact hn
    this ▸ next0 (n/2) (recBase2 zero one next0 next1 (n/2 + 1))
  else
    have : n % 2 = 1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one n) h
    have : n+2 = 2*(n/2 + 1) + 1 := by rw [this] at hn; exact hn
    this ▸ next1 (n/2) (recBase2 zero one next0 next1 (n/2 + 1))
decreasing_by exact recBase2_terminates _


end Nat
