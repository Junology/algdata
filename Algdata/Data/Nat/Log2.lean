/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

/-!
# `Classical`-free variant of `Nat.log2`
-/

namespace Nat

theorem log2_terminates' : ∀ n, n ≥ 2 → n / 2 < n
  | 2, _ => by decide
  | 3, _ => by decide
  | n+4, _ => by
    rw [Nat.div_eq, if_pos]
    refine Nat.succ_lt_succ (Nat.lt_trans ?_ (Nat.lt_succ_self _))
    exact log2_terminates' (n+2) (Nat.add_comm _ _ ▸ Nat.le.intro rfl)
    exact And.intro (Nat.zero_lt_succ 1) ‹n+4 ≥ 2›

--- axiom-free version of `Nat.log2`
@[implemented_by Nat.log2]
def log2' (n : @& Nat) : Nat :=
  if n ≥ 2 then log2' (n / 2) + 1 else 0
decreasing_by exact log2_terminates' _ ‹_›

theorem log2_eq (n : Nat) : log2' n = Nat.log2 n :=
  if h : n ≥ 2 then by
    unfold log2'; unfold Nat.log2
    rw [log2_eq (n / 2)]
  else by
    unfold log2'; unfold Nat.log2
    rw [if_neg h, if_neg h]
decreasing_by exact log2_terminates' _ ‹_›

theorem log2'_mul2 (n : Nat) : log2' (2*n.succ) = (log2' n.succ) + 1 := by
  conv =>
    lhs; unfold log2'; dsimp
    tactic => have : 2 * n.succ ≥ 2 := by {
      rw [Nat.mul_succ, Nat.add_comm]; exact Nat.le.intro rfl
    }
    rw [if_pos this]
    rw [Nat.mul_div_right _ (Nat.zero_lt_succ 1)]

#print axioms Nat.log2'_mul2

theorem zero_or_one_of_log2' (n : Nat) : n.log2' = 0 → n = 0 ∨ n = 1:= by
  cases n
  case zero => intros; exact Or.inl rfl
  case succ n =>
    unfold log2'
    cases n
    case zero => intros; exact Or.inr rfl
    case succ n =>
      have : n.succ.succ ≥ 2 := by
        conv => lhs; change n + 2
        exact Nat.add_comm _ _ ▸ Nat.le.intro rfl
      rw [if_pos this]
      intro hcontra
      exact absurd hcontra (Nat.succ_ne_zero _)

theorem ge_two_of_log2' (n : Nat) : n.log2' > 0 → n ≥ 2 := by
  unfold log2'
  cases Nat.lt_or_ge n 2
  case inl hlt =>
    rw [if_neg (Nat.not_le_of_gt hlt)]
    intro hcontra; exact absurd hcontra (Nat.not_lt_zero _)
  case inr hge =>
    rw [if_pos hge]
    intros; exact hge

end Nat