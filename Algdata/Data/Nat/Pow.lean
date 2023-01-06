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
def sqPow (a : α) (n : @& Nat) : α := loop n 1 a
  where
    loop (n : @& Nat) (result : α) (base : α) : α :=
      if h : n = 0
      then result
      else
        let res' := if n.land 1 = 0 then result else result * base
        have : Nat.shiftRight n 1 < n := Nat.shiftRight_lt h Nat.zero_lt_one
        loop (Nat.shiftRight n 1) res' (base*base)
    termination_by _ n _ _ => n

theorem sqPow_loop_eq (mul_one : ∀ (a : α), a * 1 = a) (assoc : ∀ (a b c : α), (a * b) * c = a * (b * c)) (n : Nat) (a b : α) : sqPow.loop n a b = a * sqPow b n := by
  induction n using recBase2 generalizing a b
  case zero => exact (mul_one a).symm
  case one =>
    conv =>
      unfold sqPow; unfold sqPow.loop
      rw [dif_neg Nat.one_ne_zero, dif_neg Nat.one_ne_zero]; dsimp [shiftRight]
      change sqPow.loop 0 (a*b) (b*b) = a * sqPow.loop 0 (1*b) (b*b)
      unfold sqPow.loop
      rw [dif_pos rfl, dif_pos rfl]
      rw [←assoc, mul_one]
  case next0 n h_ind =>
    unfold sqPow; unfold sqPow.loop
    have : 2 * n.succ ≠ 0 := by rw [mul_succ]; exact Nat.succ_ne_zero _
    rw [dif_neg this, dif_neg this]; dsimp
    rw [Nat.shiftRight_one, Nat.land_one]
    rw [Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 1)]
    rw [if_pos (Nat.mul_mod_right _ _)]; rw [if_pos (Nat.mul_mod_right _ _)]
    rw [h_ind]
    rfl
  case next1 n h_ind =>
    unfold sqPow; unfold sqPow.loop
    rw [dif_neg (Nat.succ_ne_zero _), dif_neg (Nat.succ_ne_zero _)]
    simp only [Nat.shiftRight_one, Nat.land_one]
    have : (2*n.succ+1)/2 = n.succ := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (y:=2) (Nat.zero_lt_succ 1)]
      have : 1 / 2 = 0 := rfl; rw [this]
      exact Nat.zero_add _
    have : (2*n.succ+1)%2 = 1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      rfl
    rw [this, ‹(2*n.succ+1)/2=n.succ›, if_neg Nat.one_ne_zero, if_neg Nat.one_ne_zero]
    rw [h_ind, h_ind]
    conv =>
      rhs; rw [←assoc a, ←assoc a, mul_one a]

theorem sqPow_zero (a : α) : sqPow a 0 = 1 := rfl

theorem sqPow_one (a : α) : sqPow a 1 = 1 * a := by
  conv =>
    lhs; unfold sqPow; unfold sqPow.loop; whnf

theorem sqPow_even (a : α) (k : Nat) : sqPow a (2*k.succ) = sqPow (a*a) k.succ := by
  have : 2 * k.succ ≠ 0 := by rw [Nat.mul_succ]; exact Nat.succ_ne_zero _
  conv =>
    lhs; unfold sqPow; unfold sqPow.loop
    rw [dif_neg this]
    dsimp
    rw [Nat.shiftRight_one, Nat.land_one]
    rw [Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 1)]
    rw [if_pos (Nat.mul_mod_right _ _)]

theorem sqPow_odd (mul_one : ∀ (a : α), a * 1 = a) (one_mul : ∀ (a : α), 1 * a = a) (assoc : ∀ (a b c : α), (a * b) * c = a * (b * c)) (a : α) (k : Nat) : sqPow a (2*k+1) = a * sqPow (a*a) k := by
  have : 2*k + 1 > 0 := Nat.zero_lt_succ _
  have : (2*k+1)/2 = k := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (y:=2) (Nat.zero_lt_succ 1)]
    have : 1 / 2 = 0 := rfl; rw [this]
    exact Nat.zero_add _
  have : (2*k+1)%2 = 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl
  conv =>
    lhs; unfold sqPow; unfold sqPow.loop
    rw [dif_neg (Nat.ne_of_gt ‹2*k+1>0›)]
    dsimp; rw [Nat.shiftRight_one, Nat.land_one]
    rw [‹(2*k+1)/2=k›, ‹(2*k+1)%2=1›, if_neg Nat.one_ne_zero]
    rw [sqPow_loop_eq mul_one assoc, one_mul]


/-!
## Comparison of powers
-/

theorem sqPow_eq_gpow {α : Type _} [OfNat α (nat_lit 1)] [HMul α α α] (mul_one : ∀ (a : α), a * 1 = a) (one_mul : ∀ (a : α), 1 * a = a) (assoc : ∀ (a b c : α), (a*b)*c = a*(b*c)) : ∀ (a : α) (n : Nat), sqPow a n = gpow a n := by
  intro a n
  induction n using recBase2 generalizing a
  case zero => intros; rfl
  case one => rw [sqPow_one, one_mul]; dsimp [gpow]; rw [mul_one]
  case next0 n h_ind =>
    conv =>
      lhs; rw [sqPow_even a n, h_ind]
    conv =>
      rhs; rw [gpow_mul one_mul assoc]; lhs; change a * (a * 1); rw [mul_one]
  case next1 n h_ind =>
    conv =>
      lhs; rw [sqPow_odd mul_one one_mul assoc, h_ind]
    conv =>
      rhs; rw [Nat.add_comm, gpow_add one_mul assoc, gpow_mul one_mul assoc a 2 n.succ]
      dsimp [gpow]
      rw [mul_one]

end Nat
