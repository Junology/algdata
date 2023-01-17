/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.Nat.Lemmas

import Algdata.Init.Nat
import Algdata.Data.Z256.Basic

/-!
# Basic lemmas on the quotient ring Z/256Z
-/

namespace ℤ256

/-!
## Equality
-/

protected
theorem eq : ∀ {x y : ℤ256}, x.val = y.val → x = y
| mk _, mk _, rfl => rfl

protected
theorem eq_of_toNat_eq : ∀ {x y : ℤ256}, x.toNat = y.toNat → x = y
| mk (.mk (.mk _ _)), mk (.mk (.mk _ _)), h => by cases h; rfl


/-!
## Basic arithmetics
-/

/-!
### Addition
-/
protected
theorem add_comm (x y : ℤ256) : x + y = y + x := by
  apply ℤ256.eq_of_toNat_eq
  conv => change (x.toNat + y.toNat) % UInt8.size = (y.toNat + x.toNat) % UInt8.size
  rw [Nat.add_comm]

@[simp]
protected
theorem zero_add (x : ℤ256) : 0 + x = x := by
  apply ℤ256.eq_of_toNat_eq
  conv => change (0 + x.toNat) % UInt8.size = x.toNat
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt x.val.val.2

@[simp]
protected
theorem add_zero (x : ℤ256) : x + 0 = x := by
  rw [ℤ256.add_comm, ℤ256.zero_add]

protected
theorem add_assoc (x y z : ℤ256) : x + y + z = x + (y + z) := by
  apply ℤ256.eq_of_toNat_eq
  conv =>
    lhs; change ((x.toNat + y.toNat) % UInt8.size + z.toNat) % UInt8.size
  conv =>
    rhs; change (x.toNat + (y.toNat + z.toNat) % UInt8.size) % UInt8.size
  simp [Nat.add_assoc]

@[simp]
protected
theorem add_sub_self_right (x y : ℤ256) : x + y - y = x := by
  apply ℤ256.eq_of_toNat_eq
  conv =>
    lhs; change ((x.toNat + y.toNat) % UInt8.size + (UInt8.size - y.toNat)) % UInt8.size
    simp; rw [Nat.add_assoc, ←Nat.add_sub_assoc (k:=y.toNat) (Nat.le_of_lt y.val.val.2)]
    rw [Nat.add_sub_self_left, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (a:=x.toNat) x.val.val.2]

@[simp]
protected
theorem add_sub_self_left (x y : ℤ256) : x + y - x = y := by
  rw [ℤ256.add_comm, ℤ256.add_sub_self_right]

protected
theorem neg_eq (x : ℤ256) : -x = 0 - x := rfl


/-!
### Multiplication
-/
protected
theorem mul_comm (x y : ℤ256) : x * y = y * x := by
  apply ℤ256.eq_of_toNat_eq
  conv => change (x.toNat * y.toNat) % UInt8.size = (y.toNat * x.toNat) % UInt8.size
  rw [Nat.mul_comm]

@[simp]
protected
theorem one_mul (x : ℤ256) : 1 * x = x := by
  apply ℤ256.eq_of_toNat_eq
  conv => change (1 * x.toNat) % UInt8.size = x.toNat
  rw [Nat.one_mul]
  exact Nat.mod_eq_of_lt x.val.val.2

@[simp]
protected
theorem mul_one (x : ℤ256) : x * 1 = x := by
  rw [ℤ256.mul_comm, ℤ256.one_mul]

protected
theorem mul_assoc (x y z : ℤ256) : x * y * z = x * (y * z) := by
  apply ℤ256.eq_of_toNat_eq
  conv =>
    lhs; change ((x.toNat * y.toNat) % UInt8.size * z.toNat) % UInt8.size
    rw [Nat.mod_mul_mod, Nat.mul_assoc]
  conv =>
    rhs; change (x.toNat * ((y.toNat * z.toNat) % UInt8.size)) % UInt8.size
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]


/-!
### Distributive law
-/

protected
theorem left_distrib (x y z : ℤ256) : x * (y + z) = x * y + x * z := by
  apply ℤ256.eq_of_toNat_eq
  conv =>
    lhs; change x.toNat * ((y.toNat + z.toNat) % UInt8.size) % UInt8.size
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod]
    rw [Nat.left_distrib]
  conv =>
    rhs; change (x.toNat * y.toNat % UInt8.size + x.toNat * z.toNat % UInt8.size) % UInt8.size
    rw [←Nat.add_mod]

protected
theorem right_distrib (x y z : ℤ256) : (x + y) * z = x * z + y * z := by
  rw [ℤ256.mul_comm (x+y) z, ℤ256.mul_comm x z, ℤ256.mul_comm y z]
  exact ℤ256.left_distrib z x y

end ℤ256


