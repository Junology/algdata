/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

import Algdata.Data.Nat.Rec

/-!
# Bit operations on Nat
-/

universe u v

namespace Nat

/-!
## Utility functions and lemmas
-/

/-- Bit-wise folding operation -/
def foldBitsL {α : Type u} (f : α → Bool → α) (init : α) (n : Nat) : α :=
  n.recBase2 (motive:=λ _ => α) init (f init true) (λ _ a => f a false) (λ _ a => f a true)

def countBits (n : Nat) : Nat := n.foldBitsL (λ n b => n + b.toUInt64.val.val) 0

def toDigitsBase2 (n : Nat) (pre : String := "0b"): String := n.foldBitsL (λ s b => s ++ if b then "1" else "0") pre

-- test
example : toDigitsBase2 0x55 "pre" = "pre1010101" := by conv => lhs; whnf

theorem or_zero (n : Nat) : n ||| 0 = n := by
  dsimp [HOr.hOr, OrOp.or, Nat.lor]; unfold Nat.bitwise
  rw [Bool.false_or, Bool.or_false, if_pos rfl, if_pos rfl, if_pos rfl]
  by_cases n = 0
  case pos h => cases h; rw [if_pos rfl]
  case neg h => rw [if_neg h]

theorem or_one_eq_add_one (n : Nat) : n % 2 = 0 → n ||| 1 = n + 1 := by
  intro hn
  have hn2_neq_1: n % 2 ≠ 1 := λ h => absurd (Eq.trans hn.symm h) Nat.zero_ne_one
  conv =>
    lhs;
    dsimp [HOr.hOr, OrOp.or, Nat.lor]; unfold bitwise
    rw [if_neg Nat.one_ne_zero, Bool.false_or, if_pos rfl]
    zeta
    rw [decide_eq_false hn2_neq_1, Bool.false_or, decide_eq_true, if_pos rfl]
    change if n = 0 then 1 else ((n/2) ||| 0) + ((n/2) ||| 0) + 1
    rw [or_zero, ←Nat.mul_two]
    rw [Nat.div_mul_cancel ((Nat.dvd_iff_mod_eq_zero 2 n).mpr hn)]
  by_cases n = 0
  case pos h => cases h; rw [if_pos rfl]
  case neg h => rw [if_neg h]

theorem shiftLeft_one (n : Nat) : n <<< 1 = 2*n := rfl

theorem shiftLeft_one_or_one (n : Nat) : (n <<< 1) ||| 1 = 2*n + 1 := by
  rw [shiftLeft_one]
  apply or_one_eq_add_one
  exact Nat.mul_mod_right 2 n

def recBits {motive : Nat → Prop} (zero : motive 0) (one : motive 1) (shift0 : ∀ (n : Nat), motive n.succ → motive (n.succ <<< 1)) (shift1 : ∀ (n : Nat), motive n.succ → motive ((n.succ <<< 1) ||| 1)) (n : Nat) : motive n := by
  induction n using recBase2
  case zero => exact zero
  case one => exact one
  case next0 => rw [←shiftLeft_one]; exact shift0 ‹_› ‹_›
  case next1 => rw [←shiftLeft_one_or_one]; exact shift1 ‹_› ‹_›


/-!
## `Classical`-free variant of `Nat.log2`
-/

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