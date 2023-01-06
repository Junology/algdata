/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Nat

/-!
# A variety of recursions on `Nat`
-/

namespace Nat

theorem inductionOn' {motive : Nat → Prop} (n : Nat) (base : motive 0) (succ : (n : Nat) → (∀ (k : Nat), k < n → motive k) → motive n) : motive n := by
  suffices ∀ k, k ≤ n → motive k
    from this n (Nat.le_refl n)
  induction n
  case zero =>
    intro k hk
    rw [Nat.le_antisymm hk (Nat.zero_le k)]
    exact base
  case succ n h_ind =>
    intro k hk
    cases Nat.lt_or_eq_of_le hk
    case inl h => exact h_ind k (Nat.le_of_lt_succ h)
    case inr h =>
      cases h
      apply succ
      exact λ k hk => h_ind k (Nat.le_of_lt_succ hk)

theorem even_or_odd (n : Nat) : (∃ (k : Nat), n = 2*k) ∨ (∃ (k : Nat), n = 2*k+1) := by
  by_cases n % 2 = 0
  case pos h =>
    apply Or.inl
    exists n / 2
    calc
      n = 2 * (n/2) + n%2 := (Nat.div_add_mod n 2).symm
      _ = 2 * (n/2) := by rw [h, Nat.add_zero]
  case neg h =>
    have : n % 2 = 1 := by
      have : n % 2 < 2 := Nat.mod_lt _ (Nat.zero_lt_succ 1)
      have : n % 2 ≤ 1 := Nat.le_of_lt_succ this
      have : n % 2 ≥ 1 := Nat.gt_zero_of_not_eq_zero h
      apply Nat.le_antisymm <;> assumption
    apply Or.inr
    exists n / 2
    calc
      n = 2 * (n/2) + n%2 := (Nat.div_add_mod n 2).symm
      _ = 2 * (n/2) + 1 := by rw [this]

theorem rec_even_odd {motive : Nat → Prop} (base : motive 0) (even : (k : Nat) → (k > 0) → motive k → motive (2*k)) (odd : (k : Nat) → motive k → motive (2*k+1)) (n : Nat) : motive n := by
  apply Nat.inductionOn' n; clear n
  case base => exact base
  case succ =>
    intro n h_ind
    cases even_or_odd n
    case inl h =>
      cases h with | intro m hm =>
      cases hm
      cases m
      case zero => rw [Nat.mul_zero]; exact base
      case succ m =>
        apply even _ (Nat.zero_lt_succ m); apply h_ind
        calc
          succ m
            < succ m + succ m := Nat.lt_add_succ _ m
          _ = 2*succ m := by simp only [Nat.add_mul 1 1 _, Nat.one_mul]
    case inr h =>
      cases h with | intro m hm =>
      cases hm
      apply odd; apply h_ind
      calc
        m ≤ m + m := Nat.le_add_left m m
        _ = 2 * m := by simp only [Nat.add_mul 1 1 m, Nat.one_mul]
        _ < 2 * m + 1 := Nat.lt_succ_self _

end Nat
