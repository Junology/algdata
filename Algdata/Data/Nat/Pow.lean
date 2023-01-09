/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Nat
import Algdata.Data.Nat.Rec

/-!
# Power functions
-/

namespace Nat

universe u
variable {α : Type u} [OfNat α (nat_lit 1)] [HMul α α α]


/-!
## Naive generic power function
-/
--- naive power
def gpow (a : α) (n : @& Nat) : α :=
  match n with
  | 0 => 1
  | (k+1) => a * gpow a k

section ExponentLaw

@[simp]
theorem gpow_zero (a : α) : gpow a 0 = 1 := rfl

@[simp]
theorem gpow_one (mul_one : ∀ (a : α), a * 1 = a) (a : α) : gpow a 1 = a := mul_one a

variable (one_mul : ∀ (a : α), 1 * a = a) (assoc : ∀ (a b c : α), (a * b) * c = a * (b * c))

--- Exponent law 1: aᵐ⁺ⁿ = aᵐaⁿ
def gpow_add (a : α) (m n : Nat) : gpow a (m+n) = gpow a m * gpow a n := by
  induction m
  case zero =>
    rw [Nat.zero_add]
    have : gpow a Nat.zero = 1 := rfl; rw [this]; clear this
    rw [one_mul]
  case succ m h_ind =>
    rw [Nat.succ_add]; dsimp [gpow]
    rw [h_ind, assoc]

--- Exponent law 2: aᵐⁿ = (aᵐ)ⁿ
def gpow_mul (a : α) (m n : Nat) : gpow a (m*n) = gpow (gpow a m) n := by
  induction n
  case zero =>
    rw [Nat.mul_zero]
    rfl
  case succ n h_ind =>
    conv => lhs; rw [Nat.mul_succ, Nat.add_comm _ m, gpow_add one_mul assoc]
    conv => rhs; dsimp [gpow]
    rw [h_ind]

end ExponentLaw


/-!
## Power using exponentiation by squaring
-/

--- exponentiation by squaring
@[specialize,inline]
def sqPow (a : α) (n : @& Nat) : α :=
  n.recBase2' (motive:=λ _ => α) 1 a $ λ n x => if n % 2 = 1 then a * x * x else x * x


/-!
## Comparison of powers
-/

theorem sqPow_eq_gpow {α : Type _} [OfNat α (nat_lit 1)] [HMul α α α] (mul_one : ∀ (a : α), a * 1 = a) (one_mul : ∀ (a : α), 1 * a = a) (assoc : ∀ (a b c : α), (a*b)*c = a*(b*c)) : ∀ (a : α) (n : Nat), sqPow a n = gpow a n := by
  intro a n
  unfold sqPow
  induction n using recBase2' generalizing a
  case zero => rfl
  case one =>
    rw [recBase2'_one]
    exact (mul_one a).symm
  case div2 n h_ind =>
    rw [recBase2'_add2]
    rw [h_ind a]
    by_cases n % 2 = 1
    case pos hodd =>
      rw [if_pos hodd]
      conv =>
        lhs; change gpow a (n/2 + 2) * gpow a (n/2 + 1)
        rw [←gpow_add one_mul assoc]
      apply congrArg
      conv =>
        lhs; rw [Nat.add_assoc, ←Nat.add_assoc 2 (n/2) 1, Nat.add_comm 2, Nat.add_assoc _ 2 1, ←Nat.add_assoc]
        rw [←Nat.mul_two, Nat.mul_comm, Nat.add_comm 2 1, ←Nat.add_assoc, ←hodd]
        rw [Nat.div_add_mod]
    case neg heven =>
      rw [if_neg heven]
      rw [←gpow_add one_mul assoc]
      have : n % 2 = 0 := Or.resolve_right (Nat.mod_two_eq_zero_or_one n) heven
      apply congrArg
      conv =>
        lhs; rw [Nat.add_assoc, ←Nat.add_assoc 1, Nat.add_comm 1, Nat.add_assoc _ 1 1, ←Nat.add_assoc]
        rw [←Nat.mul_two, Nat.mul_comm, ←Nat.add_zero (2*(n/2)), ←this]
        rw [Nat.div_add_mod]

end Nat
