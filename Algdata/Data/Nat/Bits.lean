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
  n.recBase2 (motive:=λ _ => α) init (f init true) (λ n a => f a (n % 2 == 1))

def countBits (n : Nat) : Nat := n.foldBitsL (λ n b => n + b.toUInt64.val.val) 0

def toDigitsBase2 (n : Nat) (pre : String := "0b"): String := n.foldBitsL (λ s b => s ++ if b then "1" else "0") pre

-- test
example : countBits 0b1001010111 = 6 := rfl
example : toDigitsBase2 0x55 "pre" = "pre1010101" := rfl

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

def recBits {motive : Nat → Prop} (zero : motive 0) (one : motive 1) (shift : ∀ (n : Nat), motive (n >>> 1) → motive n) (n : Nat) : motive n := by
  induction n using recBase2
  case zero => exact zero
  case one => exact one
  case div2 n h_ind =>
    apply shift (n+2)
    have : (n+2) >>> 1 = n/2 + 1 := calc
      (n+2) >>> 1 = (n+2)/2 := Nat.shiftRight_one _
      _           = (n/2) + 1 := Nat.add_div_right _ (Nat.zero_lt_succ 1)
    exact this ▸ h_ind

/-!
## `Classical`-free variant of `Nat.log2`
-/

/--
A `Classical`-free version of `Nat.log2.
It also avoids the use of well-founded recursion by using `Nat.recComplete`.
As a result, Lean can realize the second equality in contrast to the first:
```lean
example : log2 0b1000 = 3 := rfl    -- error
example : log2'' 0b1000 = 3 := rfl  -- ok
```
-/
@[implemented_by Nat.log2]
def log2' (n : @& Nat) : Nat :=
  n.recBase2 (motive:=λ _=>Nat) 0 0 $ λ _ x => x+1

example : log2' 0x100 = 8 := rfl
example : log2' 0x1FF = 8 := rfl
example : log2' 0x200 = 9 := rfl

theorem log2'_eq (n : Nat) : log2' n = Nat.log2 n := by
  unfold log2'
  induction n using recBase2
  case zero => rfl
  case one => rfl
  case div2 n h_ind =>
    rw [recBase2_div2, h_ind]
    conv =>
      rhs; unfold log2; rw [if_pos (Nat.le_add_left 2 n), Nat.add_div_right n (Nat.zero_lt_succ 1)]

theorem log2'_mul2 (n : Nat) : log2' (2*n.succ) = (log2' n.succ) + 1 := by
  conv =>
    lhs; rw [Nat.mul_succ 2 n]; unfold log2'; rw [recBase2_div2]
    change log2' (2*n/2 + 1) + 1
    rw [Nat.mul_div_right n (Nat.zero_lt_succ 1)]

#print axioms Nat.log2'_mul2

theorem zero_or_one_of_log2' : ∀ (n : Nat), n.log2' = 0 → n = 0 ∨ n = 1
| 0, _ => Or.inl rfl
| 1, _ => Or.inr rfl
| _+2, h => by
  conv at h => unfold log2'; rw [recBase2_div2]
  cases h

theorem ge_two_of_log2' : ∀ (n : Nat), n.log2' > 0 → n ≥ 2
| 0, h => by unfold log2' at h; rw [recBase2_zero] at h; cases h
| 1, h => by unfold log2' at h; rw [recBase2_one] at h; cases h
| _+2, _ => by rw [Nat.add_comm]; exact Nat.le.intro rfl

end Nat