/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Data.Nat.Bits
import Algdata.Data.Array.Lemmas

/-!
# Common interface for unsinged integers
-/

/-!
## Definition
-/

class UInt (α : Type) [(n : Nat) → OfNat α n] extends Add α, Sub α, Mul α, Neg α, OrOp α, AndOp α, Xor α, Complement α, ShiftLeft α, ShiftRight α where
  toNat : α → Nat
  ofBool : Bool → α
  length : Nat
  toNat_ofNat : ∀ (n : Nat), toNat (OfNat.ofNat n) = n % 2^length
  ofNat_toNat : ∀ (a : α), OfNat.ofNat (toNat a) = a
  ofBool_true : ofBool true = 1
  ofBool_false : ofBool false = 0
  toNat_add : ∀ (a b : α), toNat (a + b) = (toNat a + toNat b) % 2^length
  toNat_sub : ∀ (a b : α), toNat (a - b) = (toNat a + (2^length - toNat b)) % 2^length
  toNat_mul : ∀ (a b : α), toNat (a * b) = (toNat a * toNat b) % 2^length
  toNat_lor : ∀ (a b : α), toNat (a ||| b) = toNat a ||| toNat b
  toNat_land : ∀ (a b : α), toNat (a &&& b) = toNat a &&& toNat b
  toNat_xor : ∀ (a b : α), toNat (a ^^^ b) = toNat a ^^^ toNat b
  toNat_shiftLeft : ∀ (a b : α), toNat (a <<< b) = (toNat a <<< (toNat b % length)) % 2^length
  toNat_shiftRight : ∀ (a b : α), toNat (a >>> b) = toNat a >>> (toNat b % length)
  neg_eq : ∀ (a : α), -a = 0 - a
  complement_eq : ∀ (a : α), ~~~a = 0 - (a+1)


namespace UInt

variable {α : Type} [(n : Nat) → OfNat α n] [UInt α]

/-!
## Basic equalities and inequalities
-/

/-- `UInt.toNat` is injective. -/
theorem toNat_inj : ∀ {a b : α}, toNat a = toNat b → a = b := by
  intro a b h
  rw [←ofNat_toNat a, ←ofNat_toNat b, h]

/-- The image of `UInt.toNat` do not exceed `2^length`. -/
theorem toNat_lt (a : α) : toNat a < 2^(length α) := by
  rw [←ofNat_toNat a, toNat_ofNat]
  exact Nat.mod_lt (toNat a) (y:=2^(length α)) (Nat.pos_pow_of_pos _ (Nat.zero_lt_succ 1))

theorem toNat_zero : toNat (α:=α) 0 = (nat_lit 0) :=
  toNat_ofNat (α:=α) 0 ▸ Nat.mod_eq_of_lt (Nat.pos_pow_of_pos (length α) (by decide))

theorem toNat_complement (a : α) : toNat (~~~a) = 2^length α - (toNat a + 1) := by
  simp [complement_eq, toNat_sub, toNat_add, toNat_zero]
  have : toNat (1 : α) = 1 % 2^length α := toNat_ofNat 1
  rw [this, Nat.add_mod_mod]
  cases Nat.lt_or_eq_of_le (toNat_lt a)
  case inl h =>
    have : toNat a + 1 < 2^length α := h
    have : 2^length α - (toNat a + 1) < 2^length α :=
      Nat.sub_lt_self (Nat.zero_lt_succ _) (toNat_lt a)
    rw [
      Nat.mod_eq_of_lt ‹toNat a + 1 < 2^length α›,
      Nat.mod_eq_of_lt ‹2^length α - (toNat a + 1) < 2^length α›
    ]
  case inr h =>
    have : toNat a + 1 = 2^length α := h
    simp [this]

/-- `toNat a = 0` provided `length α = 0`. -/
theorem toNat_of_length_eq_zero : length α = 0 → ∀ (a : α), UInt.toNat a = 0 :=
  λ h a => calc
    UInt.toNat a
      = UInt.toNat (OfNat.ofNat (α:=α) (UInt.toNat a)) := by rw [UInt.ofNat_toNat]
    _ = UInt.toNat a % 2^length α := UInt.toNat_ofNat ..
    _ = UInt.toNat a % 1 := by rw [h, Nat.pow_zero]
    _ = 0 := Nat.mod_one ..

/-- The type `α` is subsingleton if `UInt.length α = 0`. -/
theorem eq_of_length_eq_zero : length α = 0 → ∀ (a b : α), a = b := by
  intro h a b; apply UInt.toNat_inj; simp only [toNat_of_length_eq_zero h]

protected
theorem ofNat_add (m n : Nat) : OfNat.ofNat (α:=α) m + OfNat.ofNat n = OfNat.ofNat (m+n) := by
  apply UInt.toNat_inj
  simp only [toNat_add, toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]


/-!
## Arithmetic operators
-/

protected
theorem add_comm (a b : α) : a + b = b + a := by
  apply toNat_inj; simp [toNat_add]; rw [Nat.add_comm]

protected
theorem add_assoc (a b c : α) : a + b + c = a + (b + c) := by
  apply toNat_inj; simp [toNat_add]; rw [Nat.add_assoc]

protected
theorem add_zero (a : α) : a + 0 = a := by
  apply toNat_inj; simp [toNat_add, toNat_zero]; exact Nat.mod_eq_of_lt (toNat_lt a)

protected
theorem zero_add (a : α) : 0 + a = a := by
  apply toNat_inj; simp [toNat_add, toNat_zero]; exact Nat.mod_eq_of_lt (toNat_lt a)

protected
theorem add_eq_xor {a b : α} : a &&& b = 0 → a + b = a ^^^ b := by
  intro h
  apply toNat_inj; simp [toNat_add, toNat_xor]
  have : toNat a &&& toNat b = 0 :=
    toNat_land a b ▸ h ▸ toNat_zero
  rw [Nat.add_eq_xor this]
  have : toNat a ^^^ toNat b < 2^length α
    := Nat.bitwise_lt_exp2 bne (toNat_lt a) (toNat_lt b)
  rw [Nat.mod_eq_of_lt this]

protected
theorem sub_of_toNat_ge_toNat {a b : α} : UInt.toNat a ≥ UInt.toNat b → UInt.toNat (a-b) = UInt.toNat a - UInt.toNat b := by
  intro hgt
  rw [
    UInt.toNat_sub,
    ←Nat.add_sub_assoc (Nat.le_of_lt $ UInt.toNat_lt b),
    Nat.sub_add_comm hgt,
    Nat.add_mod_right,
    Nat.mod_eq_of_lt (trans (Nat.sub_le ..) (UInt.toNat_lt a))
  ]

protected
theorem mul_comm (a b : α) : a * b = b * a := by
  apply toNat_inj; simp [toNat_mul]; rw [Nat.mul_comm]

protected
theorem mul_assoc (a b c : α) : a * b * c = a * (b * c) := by
  apply toNat_inj; simp [toNat_mul]
  conv => lhs; rw [Nat.mod_mul_mod]
  conv => rhs; rw [Nat.mul_comm, Nat.mod_mul_mod, Nat.mul_comm]
  rw [Nat.mul_assoc]

protected
theorem mul_zero (a : α) : a * 0 = (0 : α) := by
  apply toNat_inj; simp [toNat_mul, toNat_zero]

protected
theorem zero_mul (a : α) : 0 * a = (0 : α) := by
  apply toNat_inj; simp [toNat_mul, toNat_zero]

protected
theorem add_mul (a b c : α) : (a + b) * c = a * c + b * c := by
  apply toNat_inj; simp [toNat_add, toNat_mul, Nat.mod_mul_mod, Nat.add_mul]

protected
theorem mul_add (a b c : α) : a * (b + c) = a * b + a * c := by
  apply toNat_inj; simp [toNat_add, toNat_mul]
  conv => lhs; rw [Nat.mul_comm, Nat.mod_mul_mod, Nat.mul_comm, Nat.mul_add]

@[simp]
protected
theorem sub_self (a : α) : a - a = 0 := by
  apply toNat_inj; simp [toNat_sub, toNat_zero]
  rw [ ←Nat.add_sub_assoc (Nat.le_of_lt (toNat_lt a))]
  rw [Nat.add_comm, Nat.add_sub_cancel, Nat.mod_self]

protected
theorem add_sub_assoc (a b c : α) : a + b - c = a + (b - c) := by
  apply toNat_inj; simp [toNat_add, toNat_sub, Nat.add_assoc]

@[simp]
protected
theorem add_neg (a b : α) : a + -b = a - b := by
  rw [neg_eq, ←UInt.add_sub_assoc, UInt.add_zero]

protected
theorem neg_add (a b : α) : -a + b = b - a := by
  rw [UInt.add_comm, UInt.add_neg]

protected
theorem add_neg_self (a : α) : a + -a = 0 :=
  trans (UInt.add_neg a a) (UInt.sub_self a)

@[simp]
protected
theorem neg_add_self (a : α) : -a + a = 0 :=
  trans (UInt.neg_add a a) (UInt.sub_self a)

@[simp]
protected
theorem neg_neg (a : α) : -(-a) = a := calc
  -(-a) = -(-a) + 0 := (UInt.add_zero _).symm
  _     = -(-a) + (-a + a) := by rw [UInt.neg_add_self]
  _     = (-(-a) + -a) + a := by rw [UInt.add_assoc]
  _     = 0 + a := by rw [UInt.neg_add_self]
  _     = a := UInt.zero_add a


/-!
## Bit operators
-/

/-- `OrOp.or` is idempotent. -/
@[simp]
protected
theorem lor_self (a : α) : a ||| a = a :=
  toNat_inj (toNat_lor a a ▸ Nat.lor_self (toNat a))

/-- `OrOp.or` is commutative. -/
protected
theorem lor_comm (a b : α) : a ||| b = b ||| a :=
  toNat_inj (toNat_lor a b ▸ toNat_lor b a ▸ Nat.lor_comm (toNat a) (toNat b))

/-- `OrOp.or` is associative. -/
protected
theorem lor_assoc (a b c : α) : a ||| b ||| c = a ||| (b ||| c) := by
  apply toNat_inj; simp [toNat_lor, Nat.lor_assoc]

/-- `0` is the right unit of `OrOp.or`. -/
@[simp]
protected
theorem lor_zero (a : α) : a ||| 0 = a :=
  toNat_inj (toNat_lor a 0 ▸ (toNat_zero (α:=α)).symm ▸ Nat.lor_zero _)

/-- `0` is the left unit of `OrOp.or`. -/
@[simp]
protected
theorem zero_lor (a : α) : 0 ||| a = a :=
  toNat_inj (toNat_lor 0 a ▸ (toNat_zero (α:=α)).symm ▸ Nat.zero_lor _)

/-- `AndOp.and` is idempotent. -/
@[simp]
protected
theorem land_self (a : α) : a &&& a = a :=
  toNat_inj (toNat_land a a ▸ Nat.land_self (toNat a))

/-- `AndOp.and` is commutative. -/
protected
theorem land_comm (a b : α) : a &&& b = b &&& a :=
  toNat_inj (toNat_land a b ▸ toNat_land b a ▸ Nat.land_comm _ _)

/-- `AndOp.and` is associative. -/
protected
theorem land_assoc (a b c : α) : a &&& b &&& c = a &&& (b &&& c) := by
  apply toNat_inj
  simp [toNat_land, Nat.land_assoc]

/-- `0` is a right annihilator wrt `AndOp.and`. -/
@[simp]
protected
theorem land_zero (a : α) : a &&& 0 = (0 : α) :=
  toNat_inj (toNat_land a 0 ▸ (toNat_zero (α:=α)).symm ▸ Nat.land_zero _)

/-- `0` is a left annihilator wrt `AndOp.and`. -/
protected
theorem zero_land (a : α) : 0 &&& a = (0 : α) :=
  toNat_inj (toNat_land 0 a ▸ (toNat_zero (α:=α)).symm ▸ Nat.zero_land _)

/-- `Xor.xor` is nilpotent. -/
@[simp]
protected
theorem xor_self (a : α) : a ^^^ a = (0 : α) :=
  toNat_inj (toNat_xor a a ▸ (toNat_zero (α:=α)).symm ▸ Nat.xor_self _)

/-- `Xor.xor` is commutative. -/
protected
theorem xor_comm (a b : α) : a ^^^ b = b ^^^ a :=
  toNat_inj (toNat_xor a b ▸ toNat_xor b a ▸ Nat.xor_comm _ _)

/-- `Xor.xor` is associative. -/
protected
theorem xor_assoc (a b c : α) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  apply toNat_inj
  simp [toNat_xor, Nat.xor_assoc]

/-- `0` is the right unit of `Xor.xor`. -/
@[simp]
protected
theorem xor_zero (a : α) : a ^^^ 0 = a :=
  toNat_inj (toNat_xor a 0 ▸ (toNat_zero (α:=α)).symm ▸ Nat.xor_zero _)

/-- `0` is the left unit of `Xor.xor`. -/
@[simp]
protected
theorem zero_xor (a : α) : 0 ^^^ a = a :=
  toNat_inj (toNat_xor 0 a ▸ (toNat_zero (α:=α)).symm ▸ Nat.zero_xor _)

/-- `AndOp.and` is left distributive to `Xor.xor`. -/
protected
theorem land_xor (a b c : α) : a &&& (b ^^^ c) = a &&& b ^^^ a &&& c := by
  apply toNat_inj; simp [toNat_land, toNat_xor]

/-- `AndOp.and` is right distributive to `XOr.xor`. -/
protected
theorem xor_land (a b c : α) : (a ^^^ b) &&& c = a &&& c ^^^ b &&& c := by
  apply toNat_inj; simp [toNat_land, toNat_xor]

/-- `Complement.complement` is involutive. -/
protected
theorem complement_complement (a : α) : ~~~(~~~a) = a := by
  apply toNat_inj
  simp [toNat_complement]
  calc
    2^length α - (2^length α - (toNat a + 1) + 1)
      = 2^length α - (2^length α - toNat a - 1 + 1) := rfl
    _ = 2^length α - (2^length α - toNat a) := by rw [Nat.sub_add_cancel (Nat.sub_pos_of_lt (toNat_lt a))]
    _ = toNat a := Nat.sub_sub_self (Nat.le_of_lt (toNat_lt a))

/-- `Complement.complement` is injective. -/
protected
theorem complement_inj (a b : α) : ~~~a = ~~~b → a = b := by
  intro h; rw [←UInt.complement_complement a, ←UInt.complement_complement b, h]

/-- `ShiftRight.shiftRight` is right unital; i.e. zero shift. -/
protected
theorem shiftRight_zero (a : α) : a >>> 0 = a := by
  apply UInt.toNat_inj
  simp only [UInt.toNat_shiftRight, UInt.toNat_ofNat 0, Nat.zero_mod]
  rfl

/-- `ShiftLeft.shiftLeft` is left unital; i.e. zero shift. -/
protected
theorem shiftLeft_zero (a : α) : a <<< 0 = a := by
  apply UInt.toNat_inj
  simp only [UInt.toNat_shiftLeft, UInt.toNat_ofNat 0]
  simp only [Nat.zero_mod, Nat.shiftLeft_zero, Nat.mod_eq_of_lt (UInt.toNat_lt a)]

/-- `ShiftRight.shiftRight` is (conditionally) additive wrt the second variable. -/
protected
theorem shiftRight_shiftRight (a b c : α) : toNat b + toNat c < length α → (a >>> b) >>> c = a >>> (b+c) := by
  intro h
  apply toNat_inj
  simp [toNat_shiftRight, toNat_add]
  rw [
    Nat.mod_eq_of_lt (trans (Nat.le_add_right (toNat b) (toNat c)) h),
    Nat.mod_eq_of_lt (trans (Nat.le_add_left (toNat c) (toNat b)) h),
    Nat.mod_eq_of_lt (trans h (Nat.exp_lt_pow _ (by decide))),
    Nat.mod_eq_of_lt h
  ]

/-- `ShiftLeft.shiftLeft` is (conditionally) additive wrt the second variable. -/
protected
theorem shiftLeft_shiftLeft (a b c : α) : toNat b + toNat c < length α → (a <<< b) <<< c = a <<< (b+c) := by 
  intro h
  apply toNat_inj
  simp [toNat_shiftLeft, toNat_add]
  rw [
    Nat.mod_eq_of_lt (trans (Nat.le_add_right (toNat b) (toNat c)) h),
    Nat.mod_eq_of_lt (trans (Nat.le_add_left (toNat c) (toNat b)) h),
    Nat.mod_eq_of_lt (trans h (Nat.exp_lt_pow _ (by decide))),
    Nat.mod_eq_of_lt h,
    Nat.mod_mul_mod,
    Nat.mul_assoc (toNat a),
    Nat.pow_add
  ]

theorem shiftLeft_shiftLeft_comm (a b c : α) : (a <<< b) <<< c = (a <<< c) <<< b := by
  apply toNat_inj; simp [toNat_shiftLeft, toNat_add]
  simp only [Nat.mod_mul_mod, Nat.mul_assoc]
  rw [Nat.mul_comm (2^(toNat b % length α))]

protected
theorem lor_shiftRight (a b c : α) : (a ||| b) >>> c = a >>> c ||| b >>> c := by
  apply toNat_inj; simp [toNat_shiftRight, toNat_lor]

protected
theorem land_shiftRight (a b c : α) : (a &&& b) >>> c = a >>> c &&& b >>> c := by
  apply toNat_inj; simp [toNat_shiftRight, toNat_land]

protected
theorem xor_shiftRight (a b c : α) : (a ^^^ b) >>> c = a >>> c ^^^ b >>> c := by
  apply toNat_inj; simp [toNat_shiftRight, toNat_xor]

protected
theorem lor_shiftLeft (a b c : α) : (a ||| b) <<< c = a <<< c ||| b <<< c := by
  apply toNat_inj; simp only [toNat_shiftLeft, toNat_lor]
  conv =>
    lhs; change (toNat a ||| toNat b) <<< (toNat c % length α) % 2^length α
    rw [Nat.lor_shiftLeft]
  simp [Nat.lor_mod_two_pow]

protected
theorem land_shiftLeft (a b c : α) : (a &&& b) <<< c = a <<< c &&& b <<< c := by
  apply toNat_inj; simp only [toNat_shiftLeft, toNat_land]
  conv =>
    lhs; change (toNat a &&& toNat b) <<< (toNat c % length α) % 2^length α
    rw [Nat.land_shiftLeft]
  simp [Nat.land_mod_two_pow]

protected
theorem xor_shiftLeft (a b c : α) : (a ^^^ b) <<< c = a <<< c ^^^ b <<< c := by
  apply toNat_inj; simp only [toNat_shiftLeft, toNat_xor]
  conv =>
    lhs; change (toNat a ^^^ toNat b) <<< (toNat c % length α) % 2^length α
    rw [Nat.xor_shiftLeft]
  simp [Nat.xor_mod_two_pow]


/-!
## Bit access
-/

/-- Get th `i`-th bit as `Bool`. -/
protected
def getBit (a : α) (i : Nat) : Bool := (toNat a).getBit i

/-- The binary representation of `0` must contain only zeros. -/
@[simp]
protected
theorem getBit_zero : ∀ i, UInt.getBit (0 : α) i = false := by
  unfold UInt.getBit; simp [toNat_zero]

@[simp]
protected
theorem getBit_one : ∀ i, UInt.getBit (1 : α) i = (decide (0 < length α) && decide (i = 0)) := by
  intro i
  cases Nat.eq_zero_or_pos (length α)
  case inl hzero =>
    simp only [hzero, decide_eq_false, Bool.false_and]
    calc
      UInt.getBit (α:=α) 1 i
        = UInt.getBit (α:=α) 0 i := by rw [UInt.eq_of_length_eq_zero hzero 1 0]
      _ = false := UInt.getBit_zero i
  case inr hpos =>
    rw [decide_eq_true hpos, Bool.true_and]
    dsimp [UInt.getBit]; rw [UInt.toNat_ofNat]
    have := calc
      1 ≤ length α := hpos
      _ < 2^length α := Nat.exp_lt_pow _ .refl
    rw [Nat.mod_eq_of_lt this]
    calc
      Nat.getBit 1 i = decide (0 = i) := Nat.getBit_two_pow 0 i
      _              = decide (i = 0) := decide_eq_decide_of_iff ⟨Eq.symm, Eq.symm⟩

/-- All the bits higher than `UInt.length α` are `false`. -/
protected
theorem getBit_high (a : α) : ∀ (i : Nat), i ≥ length α → UInt.getBit a i = false :=
  Nat.getBit_high (toNat_lt a)

@[simp]
protected
theorem getBit_lor (x y : α) : ∀ i, UInt.getBit (x ||| y) i = (UInt.getBit x i || UInt.getBit y i) := by
  intro i; unfold UInt.getBit; rw [toNat_lor]
  conv => lhs; change (Nat.bitwise or (toNat x) (toNat y)).getBit i; rw [Nat.bitwise_getBit]

@[simp]
protected
theorem getBit_land (x y : α) : ∀ i, UInt.getBit (x &&& y) i = (UInt.getBit x i && UInt.getBit y i) := by
  intro i; unfold UInt.getBit; rw [toNat_land]
  conv => lhs; change (Nat.bitwise and (toNat x) (toNat y)).getBit i; rw [Nat.bitwise_getBit]

@[simp]
protected
theorem getBit_xor (x y : α) : ∀ i, UInt.getBit (x ^^^ y) i = (bne (UInt.getBit x i) (UInt.getBit y i)) := by
  intro i; unfold UInt.getBit; rw [toNat_xor]
  conv => lhs; change (Nat.bitwise bne (toNat x) (toNat y)).getBit i; rw [Nat.bitwise_getBit]

@[simp]
protected
theorem getBit_complement (x : α) : ∀ i, UInt.getBit (~~~x) i = (UInt.getBit x i != decide (i < length α)) := by
  intro i
  unfold UInt.getBit
  rw [UInt.toNat_complement, Nat.add_comm, Nat.sub_add_eq]
  have : 2^length α - 1 - UInt.toNat x = (2^length α - 1) ^^^ UInt.toNat x := by
    apply Nat.sub_eq_xor
    rw [Nat.land_comm, Nat.land_exp2_sub_one, Nat.mod_eq_of_lt (UInt.toNat_lt x)]
  rw [this, Nat.xor_getBit, Nat.getBit_pred_two_pow, Bool.bne_comm]

@[simp]
protected
theorem getBit_shiftLeft (x y : α) : ∀ i, UInt.getBit (x <<< y) i = (decide (i < length α) && decide (i ≥ UInt.toNat y % length α) && UInt.getBit x (i - UInt.toNat y % length α)) := by
  intro i; unfold UInt.getBit
  rw [UInt.toNat_shiftLeft, Nat.getBit_mod_two_pow, Nat.shiftLeft_getBit, Bool.and_assoc]

/-- Two terms equal to each other if and only if they have the same bit representation. -/
protected
theorem bitext (a b : α) : (∀ i, i < length α → UInt.getBit a i = UInt.getBit b i) → a = b :=
  λ h =>
    have : ∀ i, UInt.getBit a i = UInt.getBit b i :=
      λ i => (Nat.lt_or_ge i (length α)).elim (h i) (λ h => trans (UInt.getBit_high a i h) (UInt.getBit_high b i h).symm)
    toNat_inj (Nat.bitext this)

/--
Binary representation for `UInt` types.
@warning Just for debug use.
-/
@[specialize]
def binRepr {α : Type} [(n : Nat) → OfNat α n] [UInt α] (x : α) : String :=
  let rec aux : Nat → String
  | 0 => ""
  | (n+1) => (if UInt.getBit x n then "1" else "0") ++ aux n
  aux (UInt.length α)


/-!
## Branchless conditional
-/

@[inline]
protected
def when (cond : Bool) (a : α) : α :=
  ((0 : α) - UInt.ofBool cond) &&& a

protected
theorem when_true_eq (a : α) : UInt.when true a = a := by
  unfold UInt.when
  apply UInt.bitext
  intro i hi
  have : (0 : α) - 1 = ~~~(0 : α) := by
    rw [UInt.complement_eq, UInt.zero_add]
  rw [UInt.ofBool_true, this, UInt.getBit_land, UInt.getBit_complement]
  simp [decide_eq_true hi, UInt.getBit_zero]

protected
theorem when_false_eq (a : α) : UInt.when false a = 0 := by
  unfold UInt.when; rw [UInt.ofBool_false, UInt.sub_self, UInt.zero_land a]


/-!
## Bit counting
-/

/--
`bitmask n` is the value whose `i`-th bit is `true` precisely if the `n`-th bit of `i` is `true`.
Hence, we have
```lean
#eval binRepr $ bitmask (0 : UInt8) -- "10101010"
#eval binRepr $ bitmask (1 : UInt8) -- "11001100"
#eval binRepr $ bitmask (2 : UInt8) -- "11110000"
#eval binRepr $ bitmask (3 : UInt8) -- "00000000"
```
-/
@[inline, specialize]
def bitmask (n : α) : α :=
  let rec @[specialize] aux : Nat → α
  | 0 => 0
  | (k+1) => aux k ^^^ ((OfNat.ofNat k >>> n &&& 1) <<< OfNat.ofNat k)
  aux (length α)

theorem getBit_bitmask (n : α) (i : Nat) : toNat n < length α → UInt.getBit (bitmask n) i = (i < length α && i.getBit (toNat n)) := by
  intro hn
  suffices ∀ k, k ≤ length α → UInt.getBit (bitmask.aux n k) i = (i < k && i.getBit (toNat n)) 
    from this (length α) Nat.le.refl
  intro k hk; induction k
  case zero =>
    conv => lhs; dsimp [bitmask.aux, UInt.getBit]; rw [toNat_zero]
    simp [bitmask.aux, Nat.not_lt_zero i]
  case succ k h_ind =>
    have : k < 2^length α := trans (Nat.le_of_succ_le hk) (Nat.exp_lt_pow _ Nat.le.refl)
    have : 2^toNat n < 2^length α := Nat.pow_lt_pow_right Nat.le.refl hn
    have : 1 < 2^length α := calc
      1 < 2^1 := by decide
      _ ≤ 2^k.succ := Nat.pow_le_pow_of_le_right (Nat.zero_lt_succ 1) (k.one_le_succ)
      _ ≤ 2^length α := Nat.pow_le_pow_of_le_right (Nat.zero_lt_succ 1) hk
    conv =>
      lhs; simp only [UInt.getBit_xor, bitmask.aux]; rw [h_ind (Nat.le_of_succ_le hk)]
      unfold UInt.getBit
      simp only [toNat_shiftLeft, toNat_land, toNat_shiftRight, toNat_ofNat k, toNat_ofNat 1]
      rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt ‹k < 2^length α›, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt ‹1<2^length α›]
      tactic =>
        have : (k >>> toNat n &&& 1) <<< k < 2^length α :=
          calc (k >>> toNat n &&& 1) <<< k
            _ = (k >>> toNat n &&& 1) * 2^k := Nat.shiftLeft_eq _ k
            _ ≤ 1*2^k := Nat.mul_le_mul_right _ $ by rw [Nat.land_one]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.zero_lt_succ 1))
            _ = 2^k := Nat.one_mul _
            _ < 2^length α := Nat.pow_lt_pow_right Nat.le.refl hk
      rw [Nat.mod_eq_of_lt this]
      rhs; rw [Nat.shiftLeft_getBit, Nat.land_getBit, Nat.shiftRight_getBit]
      change decide (i ≥ k) && (k.getBit (i-k+toNat n) && Nat.getBit (2^0) (i-k))
      rw [Nat.getBit_two_pow, ←and_decideEq (λ x => Nat.getBit k (x + toNat n))]
      tactic =>
        have : 0 = i-k ↔ i ≤ k :=
          ⟨Nat.le_of_sub_eq_zero ∘ Eq.symm, Eq.symm ∘ Nat.sub_eq_zero_of_le⟩
        have : (i ≥ k ∧ i ≤ k) ↔ i = k :=
          ⟨λ h => Nat.le_antisymm h.right h.left, λ h => by cases h; exact ⟨Nat.le.refl, Nat.le.refl⟩⟩
      rw [decide_eq_decide_of_iff ‹0=i-k ↔ i≤k›, Bool.and_comm _ (decide _), ←Bool.and_assoc]
      rw [decide_and_decide, decide_eq_decide_of_iff ‹(i≥k ∧ i≤k) ↔ i=k›]
      rw [Nat.zero_add, ←decideEq_and (f:=λ x => Nat.getBit x (toNat n))]
    rw [←Bool.bne_and]
    cases Nat.lt_or_ge i k
    case inl hlt =>
      rw [decide_eq_true hlt, decide_eq_false (Nat.ne_of_lt hlt), decide_eq_true (Nat.lt_succ_of_lt hlt)]
      rfl
    case inr hge =>
      cases Nat.lt_or_eq_of_le hge
      case inl hgt =>
        rw [decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hgt)), decide_eq_false (Nat.ne_of_gt hgt), decide_eq_false (Nat.not_lt_of_ge hgt)]
        rfl
      case inr heq => cases heq; simp

@[specialize]
def maskTable : Array α :=
  Array.ofFn (n:=Nat.log2RU (length α)) λ i => bitmask (OfNat.ofNat i.1)

theorem maskTable_size : (maskTable (α:=α)).size = Nat.log2RU (length α) := by
  unfold maskTable
  rw [Array.size_ofFn]

theorem maskTable_spec : ∀ (n i : Nat), {_ : n < (maskTable (α:=α)).size} → UInt.getBit ((maskTable (α:=α))[n]) i = ((i < length α) && Nat.getBit i n) := by
  intro n i h
  have : n < Nat.log2RU (length α) := maskTable_size (α:=α) ▸ h
  have := calc
    n < Nat.log2RU (length α) := this
    _ ≤ length α := Nat.log2RU_le_self (length α)
  have := calc
    n < length α := this
    _ < 2^(length α) := Nat.exp_lt_pow (length α) .refl
  unfold maskTable
  rw [Array.getElem_ofFn', getBit_bitmask (OfNat.ofNat n) i (toNat_ofNat (α:=α) n ▸ (Nat.mod_eq_of_lt ‹n < 2^length α›).symm ▸ ‹_›)]
  rw [toNat_ofNat (α:=α), Nat.mod_eq_of_lt ‹n < 2^length α›]

#print axioms maskTable_spec

/-- The number of `true` bits. -/
@[specialize]
def bitcnt (x : α) : α :=
  Prod.fst $ (x,1) |> (maskTable (α:=α)).foldl λ ((x,k) : α × α) (mask : α) =>
    ((x &&& ~~~mask) + ((x &&& mask) >>> k), k <<< 1)

theorem bitcnt_eq (x : α) : bitcnt x = Nat.fold (λ i (x : α) => (x &&& ~~~ bitmask (α:=α) (OfNat.ofNat i)) + ((x &&& bitmask (α:=α) (OfNat.ofNat i)) >>> ((1 : α) <<< OfNat.ofNat i))) (Nat.log2RU (length α)) x := by
  have : bitcnt x = (Prod.fst $ (x,1) |> Fin.foldAll λ (i : Fin (Nat.log2RU (length α))) ((x,k) : α × α) => ((x &&& ~~~ bitmask (OfNat.ofNat i.1)) + ((x &&& bitmask (OfNat.ofNat i.1)) >>> k), k <<< 1)) := by
    unfold bitcnt; unfold maskTable
    simp only [Array.foldl_ofFn_eq]; rfl
  rw [this]; clear this
  apply Eq.trans $ congrArg Prod.fst $ Fin.foldAll_comp_val (n:=Nat.log2RU (length α)) (f:=λ (i : Nat) ((x,k) : α × α) => ((x &&& ~~~ bitmask (OfNat.ofNat i)) + ((x &&& bitmask (OfNat.ofNat i)) >>> k), k <<< 1)) (init:=(x,1))
  generalize hn : Nat.log2RU (length α) = n
  have : Nat.fold (λ i ((x,k) : α × α) => ((x &&& ~~~ bitmask (OfNat.ofNat i)) + ((x &&& bitmask (OfNat.ofNat i)) >>> k), k <<< 1)) n (x,1) = Nat.fold (λ i ((x,_) : α × α) => ((x &&& ~~~ bitmask (α:=α) (OfNat.ofNat i)) + ((x &&& bitmask (α:=α) (OfNat.ofNat i)) >>> ((1 : α) <<< OfNat.ofNat i)), (1 : α) <<< OfNat.ofNat (i+1))) n (x,1) := by
    apply Nat.fold_congr
    case zero => dsimp; rw [UInt.shiftLeft_zero]
    case succ =>
      intro i a h; cases a with | mk x k =>
      dsimp
      apply congrArg (Prod.mk _)
      rw [UInt.shiftLeft_shiftLeft 1 (OfNat.ofNat (i+1)) 1, UInt.ofNat_add]
      . simp only [UInt.toNat_ofNat, UInt.toNat_ofNat 1]
        have : length α > 0 :=
          hn |> (length α).rec (λ (hn : 0 = n) => nomatch (trans h hn.symm)) (λ l _ _ => l.zero_lt_succ)
        have : n < length α := hn ▸ Nat.log2RU_lt_self _ ‹length α > 0›
        have : n < 2^length α := trans this (Nat.exp_lt_pow (length α) .refl)
        rw [
            Nat.mod_eq_of_lt (trans h this),
            Nat.mod_eq_of_lt (trans (trans (Nat.le_add_left 1 i) h) this)
        ]
        exact trans (r:=LE.le) (h : i+2 ≤ n) ‹n < length α›
  rw [this]; clear this
  apply Eq.symm; apply Nat.fold_hom Prod.fst _ _ _ (x,1)
  intro i z _; cases z with | mk x k => rfl

#print axioms bitcnt_eq

/--
The least significant bit; i.e. `UInt.lsb a` has `false` on all but a single bit which is the lowest non-zero bit of `a`.
For example,
```lean
#eval UInt.lsb (α:=UInt8) 0b101010 = 0b000010 -- true
#eval UInt.lsb (α:=UInt8) 0b010001 = 0b000001 -- true
```
-/
@[specialize]
protected
def lsb (a : α) : α := a ^^^ (a &&& (a-1))

@[simp]
protected
theorem toNat_lsb (a : α) : UInt.toNat (UInt.lsb a) = (UInt.toNat a).lsb := by
  if hlength : length α = 0
  then simp only [UInt.toNat_of_length_eq_zero hlength]
  else
  have hlength : length α > 0 := Nat.pos_of_ne_zero hlength
  have : 1 % 2^length α = 1 :=
    Nat.mod_eq_of_lt $ calc
      1 = 2^0 := Eq.symm $ Nat.pow_zero 2
      _ < 2^length α := Nat.pow_lt_pow_right (n:=2) .refl ‹length α > 0›
  suffices (UInt.toNat a &&& UInt.toNat (a-1)) = (UInt.toNat a &&& (UInt.toNat a - 1)) by
    unfold UInt.lsb; simp only [UInt.toNat_xor, UInt.toNat_land]
    rw [this]; rfl
  rw [UInt.toNat_sub, UInt.toNat_ofNat, ‹1%2^length α = 1›]
  cases ha : UInt.toNat a
  case zero => simp
  case succ n =>
    have := calc
      n.succ + (2^length α - 1)
        = n.succ + 2^length α - 1 :=
          by rw [Nat.add_sub_assoc (Nat.pos_pow_of_pos (n:=2) (length α) (by decide))]
      _ = (n + 2^length α).succ - 1 := by rw [Nat.succ_add]
      _ = n + 2^length α := Nat.succ_sub_one ..
    rw [this, Nat.add_mod_right]
    have := calc
      n < n.succ := n.lt_succ_self
      _ = toNat a := ha.symm
      _ < 2^length α := UInt.toNat_lt a
    simp only [Nat.mod_eq_of_lt this, Nat.succ_sub_one]

protected
theorem getBit_lsb_iff (a : α) {i : Nat} : UInt.getBit (UInt.lsb a) i = true ↔ UInt.getBit a i = true ∧ (∀ j, j < i → UInt.getBit a j = false) := by
  unfold UInt.getBit; rw [UInt.toNat_lsb]; exact Nat.lsb_getBit_iff ..

protected
theorem getBit_of_getBit_lsb (a : α) {i : Nat} : UInt.getBit (UInt.lsb a) i = true → UInt.getBit a i = true := by
  intro h; exact And.left $ (UInt.getBit_lsb_iff a).mp h

protected
theorem getBit_lower_of_lsb (a : α) {i : Nat} : UInt.getBit (UInt.lsb a) i = true → ∀ {j : Nat}, j < i → UInt.getBit a j = false := by
  intro h j; exact (And.right $ (UInt.getBit_lsb_iff a).mp h) j

@[simp]
protected
theorem lsb_zero : UInt.lsb (α:=α) 0 = 0 := by
  unfold UInt.lsb; rw [UInt.zero_land, UInt.zero_xor]

protected
theorem eq_zero_of_lsb_eq_zero (a : α) : UInt.lsb a = 0 → a = 0 := by
  intro h
  suffices UInt.toNat a = 0 by
    apply UInt.toNat_inj; rw [UInt.toNat_ofNat, Nat.zero_mod]; exact this
  have : (UInt.toNat a).lsb = 0 := by
    rw [←UInt.toNat_lsb, h, UInt.toNat_ofNat, Nat.zero_mod]
  exact Nat.eq_zero_of_lsb_eq_zero this

protected
theorem lsb_singleton (a : α) : a ≠ 0 → ∃ (i : Nat), ∀ j, UInt.getBit (UInt.lsb a) j = decide (i=j) := by
  intro ha
  have : ∃ i, UInt.getBit (UInt.lsb a) i = true := by
    cases Nat.exists_or_forall_not (UInt.getBit (UInt.lsb a) · = true) (length α)
    . cases ‹∃ i, i < length α ∧ UInt.getBit (UInt.lsb a) i = true› with
      | intro i hi => exact ⟨i, hi.right⟩
    . have hall := ‹∀ i, i < length α → ¬UInt.getBit (UInt.lsb a) i = true›
      suffices a = 0 from absurd this ha
      suffices UInt.lsb a = 0 from UInt.eq_zero_of_lsb_eq_zero a this
      suffices ∀ i, UInt.getBit (UInt.lsb a) i = false by
        apply UInt.bitext; intros; rw [this, UInt.getBit_zero]
      intro i
      cases Nat.lt_or_ge i (length α)
      case inl hlt => exact Bool.not_eq_true _ ▸ hall i hlt
      case inr hge => exact UInt.getBit_high _ _ hge
  cases this with | intro i hi =>
  suffices ∀ j, UInt.getBit (UInt.lsb a) j = decide (i = j) from ⟨i, this⟩
  intro j
  if hij : i = j
  then exact Eq.trans (hij ▸ hi) (decide_eq_true hij).symm
  else
    suffices UInt.getBit (UInt.lsb a) j ≠ true
      by rw [decide_eq_false hij]; exact eq_false_of_ne_true this
    intro hcontra
    cases Nat.lt_or_ge i j
    . have : i < j := ‹_›
      have : UInt.getBit a i = false :=
        ((UInt.getBit_lsb_iff a).mp hcontra).right i this
      have : UInt.getBit a i = true :=
        ((UInt.getBit_lsb_iff a).mp hi).left
      cases Eq.trans ‹UInt.getBit a i = false›.symm ‹UInt.getBit a i = true›
    . have : i > j := Nat.lt_of_le_of_ne ‹i ≥ j› (hij ∘ Eq.symm)
      have : UInt.getBit a j = false :=
        And.right ((UInt.getBit_lsb_iff a).mp hi) j this
      have : UInt.getBit a j = true :=
        ((UInt.getBit_lsb_iff a).mp hcontra).left
      cases Eq.trans ‹UInt.getBit a j = false›.symm ‹UInt.getBit a j = true›

/-- Count trailing zeros. -/
@[inline]
protected
def ctz [DecidableEq α] (a : α) : α :=
  let (a : α) := UInt.lsb a
  let_fun length_or_zero : α := UInt.when (a = 0) $ OfNat.ofNat (length α)
  let_fun f : α × α → α → α × α
  | (x,k), mask => (UInt.when ((a &&& mask) ≠ 0) k ||| x, k <<< 1)
  Prod.fst $ maskTable.foldl f (length_or_zero,1)

@[inline]
protected
def ctz' [DecidableEq α] (a : α) : α :=
  let a := UInt.lsb a
  let_fun f : Nat → α → α :=
    λ n x => UInt.when ((a &&& bitmask (OfNat.ofNat n)) ≠ 0) (1 <<< OfNat.ofNat (α:=α) n) ||| x
  Nat.fold f (Nat.log2RU $ length α) (UInt.when (a=0) (OfNat.ofNat (length α)))

protected
theorem ctz_eq_ctz' [DecidableEq α] : ∀ (a : α), UInt.ctz a = UInt.ctz' a := by
  let f : α → α × α → α → α × α :=
    λ a₁ z m => (UInt.when ((a₁ &&& m) ≠ 0) z.2 ||| z.1, z.2 <<< 1)
  let f' : α → Nat → α → α :=
    λ a₁ n x => UInt.when ((a₁ &&& bitmask (OfNat.ofNat n)) ≠ 0) (1 <<< OfNat.ofNat (α:=α) n) ||| x
  suffices ∀ (a x : α), (maskTable.foldl (f a) (x,1)).1 = Nat.fold (f' a) (Nat.log2RU $ length α) x
    from λ a => this (UInt.lsb a) ..
  intro a x
  conv =>
    lhs; unfold maskTable; zeta; rw [Array.foldl_ofFn_eq]; dsimp [flip, Function.comp]
    change (Fin.foldAll ((λ (n : Nat) (z : α × α) => (UInt.when (a &&& bitmask (OfNat.ofNat (α:=α) n) ≠ 0) z.2 ||| z.1, z.2 <<< 1)) ∘ Fin.val (n:=Nat.log2RU $ length α)) (x, 1)).1
    rw [Fin.foldAll_comp_val]
  conv =>
    rhs; dsimp
  clear f f'
  suffices ∀ (f : Nat → α → α) (n : Nat) (y : α), n < length α → Nat.fold (λ (i : Nat) (z : α × α) => (f i z.2 ||| z.1, z.2 <<< 1)) n (x, y) = (Nat.fold (λ (i : Nat) (x : α) => f i (y <<< OfNat.ofNat i) ||| x) n x, y <<< OfNat.ofNat n) by
    if hlength : length α = 0
    then exact UInt.eq_of_length_eq_zero hlength ..
    else
    have := this
      (f:=λ i x => UInt.when (a &&& bitmask (OfNat.ofNat i) ≠ 0) x)
      (n:=Nat.log2RU $ length α) (y:=1)
      (Nat.log2RU_lt_self (length α) (Nat.zero_lt_of_ne_zero hlength))
    exact congrArg Prod.fst this
  intro f n y hn
  induction n generalizing x y
  case zero => dsimp [Nat.fold]; rw [UInt.shiftLeft_zero]
  case succ n h_ind =>
    dsimp [Nat.fold]
    simp only [h_ind]
    have : n < length α := Nat.lt_of_succ_lt ‹n.succ < length α›
    simp only [h_ind x y this]
    suffices y <<< OfNat.ofNat n <<< 1 = y <<< OfNat.ofNat (n+1)
      from congrArg _ this
    have : toNat (OfNat.ofNat (α:=α) n) + toNat (α:=α) 1 = n+1 := by
      simp only [UInt.toNat_ofNat, UInt.toNat_ofNat 1]
      have : n % 2^length α = n := Nat.mod_eq_of_lt $ calc
        n < length α := ‹_›
        _ < 2^length α := Nat.exp_lt_pow _ .refl
      have : 1 % 2^length α = 1 := Nat.mod_eq_of_lt $ calc
        1 ≤ n+1 := Nat.le_add_left ..
        _ < length α := hn
        _ < 2^length α := Nat.exp_lt_pow _ .refl
      rw [‹n % 2^length α = n›, ‹1 % 2^length α = 1›]
    calc
      y <<< OfNat.ofNat n <<< 1
        = y <<< (OfNat.ofNat n + 1) := UInt.shiftLeft_shiftLeft y (OfNat.ofNat n) 1 (this ▸ ‹n.succ < length α›)
      _ = y <<< OfNat.ofNat (n+1) := by rw [UInt.ofNat_add]

#print axioms UInt.ctz_eq_ctz'

protected
theorem getBit_lsb_ctz [DecidableEq α] (a : α) : a ≠ 0 → UInt.getBit (UInt.lsb a) (UInt.toNat $ UInt.ctz a) = true := by
  intro ha
  have : UInt.lsb a ≠ 0 := λ h => absurd (UInt.eq_zero_of_lsb_eq_zero a h) ha
  rw [UInt.ctz_eq_ctz']; dsimp [UInt.ctz']; rw [decide_eq_false this, UInt.when_false_eq]
  cases UInt.lsb_singleton a ha with | intro i hi =>
  generalize UInt.lsb a = x at *; clear ‹a≠0› a ‹x≠0›
  let f (i : Nat) (y : α) : α := UInt.when (x &&& bitmask (OfNat.ofNat i) ≠ 0) ((1 : α) <<< OfNat.ofNat i) ||| y
  conv =>
    change UInt.getBit x (toNat $ Nat.fold f (Nat.log2RU $ length α) 0) = true
  have : UInt.getBit x i = true := (decide_eq_true (Eq.refl i) ▸ hi i)
  have : i < length α := by
    cases Nat.lt_or_ge i (length α)
    case inl hlt => exact hlt
    case inr hge =>
      have := calc
        false = UInt.getBit x i := (UInt.getBit_high x i hge).symm
        _     = true := ‹_›
      cases this
  have : 0 < length α := trans i.zero_le ‹i < length α›
  suffices UInt.toNat (Nat.fold f (Nat.log2RU $ length α) 0) = i
    by rw [this]; assumption
  have foldf_high : ∀ (n k : Nat), k ≥ n → UInt.getBit (Nat.fold f n 0) k = false := by
    intro n k hnk
    induction n generalizing k
    case zero => dsimp [Nat.fold]; exact UInt.getBit_zero k
    case succ n h_ind =>
      dsimp [Nat.fold]
      rw [UInt.getBit_lor, h_ind k (Nat.le_of_succ_le hnk), Bool.or_false]
      cases decide (x &&& bitmask (OfNat.ofNat n) ≠ 0)
      case true =>
        rw [UInt.when_true_eq, UInt.getBit_shiftLeft]
        have : UInt.getBit (1 : α) (k - toNat (OfNat.ofNat (α:=α) n) % length α) = false := by
          rw [UInt.toNat_ofNat]
          have := calc
            n % 2^length α % length α
              ≤ n % 2^length α := Nat.mod_le ..
            _ ≤ n := Nat.mod_le ..
            _ < n.succ := n.lt_succ_self
            _ ≤ k := hnk
          have : k - n % 2^length α % length α > 0 :=
            Nat.lt_sub_of_add_lt (Nat.zero_add .. ▸ this)
          rw [UInt.getBit_one, decide_eq_false (Nat.ne_of_gt this), Bool.and_false]
        simp only [this, Bool.and_false]
      case false =>
        exact UInt.when_false_eq (α:=α) .. ▸ UInt.getBit_zero (α:=α) k
  suffices ∀ (n : Nat), n < length α → ∀ (k : Nat), k < n → UInt.getBit (Nat.fold f n 0) k = i.getBit k by
    have what_is_shown :=
      this (Nat.log2RU $ length α) (Nat.log2RU_lt_self _ ‹0 < length α›)
    apply Nat.bitext; intro k
    cases Nat.lt_or_ge k (Nat.log2RU $ length α)
    case a.inl hlt => exact what_is_shown k hlt
    case a.inr hge =>
      unfold UInt.getBit at foldf_high; rw [foldf_high _ _ hge]
      suffices Nat.getBit i k = false
        from Eq.symm this
      apply Nat.getBit_high ?_ k hge
      calc
        i < length α := ‹_›
        _ ≤ 2^Nat.log2RU (length α) := Nat.le_pow2_log2RU_self _
  intro n hn k hk
  induction n generalizing k
  case zero => cases hk
  case succ n h_ind =>
    unfold Nat.fold
    conv =>
      lhs; arg 1;
      change UInt.when (x &&& bitmask (OfNat.ofNat n) ≠ 0) ((1 : α) <<< OfNat.ofNat n) ||| Nat.fold f n 0
    rw [UInt.getBit_lor]
    have : n < length α := Nat.lt_of_succ_lt hn
    have : n < 2^length α := trans this (Nat.exp_lt_pow _ .refl)
    cases hk
    case step hlt =>
      rw [h_ind (Nat.lt_of_succ_lt hn) k hlt]
      cases decide (x &&& bitmask (OfNat.ofNat n) ≠ 0)
      case false => rw [UInt.when_false_eq, UInt.getBit_zero, Bool.false_or]
      case true =>
        simp only [
          UInt.when_true_eq, UInt.getBit_shiftLeft, UInt.toNat_ofNat,
          Nat.mod_eq_of_lt ‹n < 2^length α›,
          Nat.mod_eq_of_lt ‹n < length α›
        ]
        rw [decide_eq_false (Nat.not_le_of_lt hlt)]
        simp only [Bool.false_and, Bool.and_false, Bool.false_or]
    case refl =>
      rw [foldf_high n n .refl, Bool.or_false]
      have : ∀ b, UInt.getBit (UInt.when b ((1 : α) <<< OfNat.ofNat n)) n = b := by
        intro b; cases b
        case true =>
          simp only [
            UInt.when_true_eq, UInt.getBit_shiftLeft,
            UInt.toNat_ofNat,
            Nat.mod_eq_of_lt ‹n < 2^length α›,
            Nat.mod_eq_of_lt ‹n < length α›
          ]
          rw [decide_eq_true ‹n < length α›, decide_eq_true (p:=n≥n) .refl]
          rw [Nat.sub_self, UInt.getBit_one, decide_eq_true ‹0 < length α›, decide_eq_true rfl]
          simp only [Bool.true_and]
        case false => rw [UInt.when_false_eq, UInt.getBit_zero]
      rw [this]; clear this
      suffices ∀ y, decide ((x &&& y) ≠ 0) = UInt.getBit y i by
        rw [this]
        have hgetbit := UInt.getBit_bitmask (OfNat.ofNat (α:=α) n) i
        simp only [UInt.toNat_ofNat, Nat.mod_eq_of_lt ‹n < 2^length α›] at hgetbit
        rw [decide_eq_true ‹i < length α›, Bool.true_and] at hgetbit
        exact hgetbit ‹n < length α›
      intro y
      cases hyi : UInt.getBit y i
      case true =>
        apply decide_eq_true; intro hcontra
        have := calc
          true = (true && true) := rfl
          _    = (UInt.getBit x i && UInt.getBit y i) := by rw [hi i, decide_eq_true rfl, hyi]
          _    = UInt.getBit (x &&& y) i := by rw [UInt.getBit_land]
          _    = UInt.getBit (α:=α) 0 i := by rw [hcontra]
          _    = false := UInt.getBit_zero i
        cases this
      case false =>
        apply decide_eq_false; apply not_not_intro
        apply UInt.bitext; intro j hj
        rw [UInt.getBit_zero, UInt.getBit_land, hi j]
        if hij : i = j
        then cases hij; rw [hyi, Bool.and_false]
        else rw [decide_eq_false hij, Bool.false_and]

#print axioms UInt.getBit_lsb_ctz

protected
theorem getBit_lsb_of_lt_ctz [DecidableEq α] (a : α) (i : Nat) : i < toNat (UInt.ctz a) → UInt.getBit a i = false := by
  if ha : a = 0
  then intros; rw [ha, UInt.getBit_zero]
  else
    have : ∃ i₀, ∀ j, UInt.getBit (UInt.lsb a) j = decide (i₀=j) := UInt.lsb_singleton a ha
    cases this with | intro i₀ hi₀ =>
    have : UInt.getBit (UInt.lsb a) i₀ = true := decide_eq_true (Eq.refl i₀) ▸ (hi₀ i₀)
    have ⟨_, (halow: ∀ j, j < i₀ → UInt.getBit a j = false)⟩ :=
      (UInt.getBit_lsb_iff a).mp this
    suffices UInt.toNat (UInt.ctz a) = i₀ by
      rw [this]; intro hi; exact halow _ hi
    have : decide (i₀ = toNat (UInt.ctz a)) = true :=
      hi₀ _ ▸ UInt.getBit_lsb_ctz a ha
    apply Eq.symm; exact of_decide_eq_true this

/-- The list of all indices of `true` bits. -/
@[specialize]
protected
def bitIndices (a : α) : List Nat :=
  let rec aux : Nat → List Nat 
  | 0 => []
  | (n+1) => let tail := aux n; if UInt.getBit a n then n::tail else tail
  aux (length α)

attribute [inline] UInt.bitIndices.aux

/-- An index `i : Nat` belongs to `UInt.bitIndices a` if and only if `UInt.getBit a i = true`. -/
protected
theorem Mem_bitIndices {a : α} {i : Nat} : i ∈ UInt.bitIndices a ↔ UInt.getBit a i = true := by
  suffices ∀ (n : Nat), i ∈ UInt.bitIndices.aux a n ↔ i < n ∧ UInt.getBit a i = true by 
    constructor
    case mp => intro h; exact ((this (length α)).mp h).right
    case mpr =>
      intro h
      have hi : i < length α :=
        (Nat.lt_or_ge i (length α)).elim id (λ hi => by cases (UInt.getBit_high a i hi ▸ h))
      exact (this (length α)).mpr ⟨hi, h⟩
  intro n; induction n
  case zero =>
    constructor
    . intro h; cases h
    . intro h; cases h.left
  case succ n h_ind =>
    dsimp [bitIndices.aux]
    cases hbit : UInt.getBit a n
    case false =>
      simp [h_ind]
      intro h
      have : i ≠ n := λ hcontra => by cases (hbit ▸ hcontra ▸ h)
      constructor
      . exact Nat.lt_succ_of_lt
      . intro hle; exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hle) ‹i≠n›
    case true =>
      simp
      constructor
      . intro h
        cases h
        case inl h => cases h; exact ⟨i.lt_succ_self, hbit⟩
        case inr h => exact ⟨Nat.le.step (h_ind.mp h).left, (h_ind.mp h).right⟩
      . intro h
        cases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h.left))
        case inl hlt => exact Or.inr (h_ind.mpr ⟨hlt, h.right⟩)
        case inr heq => cases heq; exact Or.inl rfl

#print axioms UInt.Mem_bitIndices

end UInt


/-!
## Instances
-/

theorem Bool.toUInt64_lt_2 : ∀ (t : Bool), t.toUInt64.1.1 < 2
| true => Nat.lt_succ_self 1
| false => Nat.zero_lt_succ 1

instance : UInt UInt8 where
  neg a := 0 - a
  toNat := UInt8.toNat
  ofBool t := ⟨t.toUInt64.1.1, trans t.toUInt64_lt_2 ((by decide) : 2 < UInt8.size)⟩
  length := 8
  toNat_ofNat n := rfl
  ofNat_toNat a :=
    match a with
    | UInt8.mk (Fin.mk a ha) => by
      have : Fin.mk (n:=UInt8.size) (a % UInt8.size) (Nat.mod_lt a (by decide)) = Fin.mk a ha :=
        Fin.eq_of_val_eq (Nat.mod_eq_of_lt ha)
      conv =>
        lhs; change UInt8.mk (Fin.mk (a % UInt8.size) (Nat.mod_lt a (by decide)))
        rw [this]
  ofBool_true := rfl
  ofBool_false := rfl
  toNat_add a b := rfl
  toNat_sub a b := rfl
  toNat_mul a b := rfl
  toNat_lor a b :=
    match a, b with
    | UInt8.mk (Fin.mk a ha), UInt8.mk (Fin.mk b hb) => by
      have : a ||| b < UInt8.size := Nat.bitwise_lt_exp2 (k:=8) or ha hb
      conv =>
        lhs; change (a ||| b) % UInt8.size
        rw [Nat.mod_eq_of_lt this]
  toNat_land a b :=
    match a, b with
    | UInt8.mk (Fin.mk a ha), UInt8.mk (Fin.mk b hb) => by
      have : a &&& b < UInt8.size := Nat.bitwise_lt_exp2 (k:=8) and ha hb
      conv =>
        lhs; change (a &&& b) % UInt8.size
        rw [Nat.mod_eq_of_lt this]
  toNat_xor a b :=
    match a, b with
    | UInt8.mk (Fin.mk a ha), UInt8.mk (Fin.mk b hb) => by
      have : a ^^^ b < UInt8.size := Nat.bitwise_lt_exp2 (k:=8) bne ha hb
      conv =>
        lhs; change (a ^^^ b) % UInt8.size
        rw [Nat.mod_eq_of_lt this]
  toNat_shiftLeft a b :=
    match a, b with
    | UInt8.mk (Fin.mk a _), UInt8.mk (Fin.mk b _) => by
      conv =>
        lhs; change (a <<< (b % 8 % UInt8.size)) % UInt8.size
        rw [Nat.mod_eq_of_lt (a:=b%8) (b:=UInt8.size) (trans (Nat.mod_lt b (y:=8) (by decide)) ((by decide) : 8 < UInt8.size))]
  toNat_shiftRight a b :=
    match a, b with
    | UInt8.mk (Fin.mk a ha), UInt8.mk (Fin.mk b _) => by
      conv =>
        lhs; change (a >>> (b % 8 % UInt8.size)) % UInt8.size
        rw [Nat.mod_eq_of_lt (a:=b%8) (b:=UInt8.size) (trans (Nat.mod_lt b (y:=8) (by decide)) ((by decide) : 8 < UInt8.size))]
        tactic =>
          have : a >>> (b%8) < UInt8.size := calc
            a >>> (b%8) ≤ a := Nat.shiftRight_le_self a _
            _           < UInt8.size := ha
        rw [Nat.mod_eq_of_lt this]
  complement_eq a := rfl
  neg_eq a := rfl


#eval List.map (α:=UInt8) UInt.ctz [
  0b0000, 0b0001, 0b0010, 0b0011, 0b0100, 0b0101, 0b0110, 0b0111,
  0b1000, 0b1001, 0b1010, 0b1011, 0b1100, 0b1101, 0b1110, 0b1111
]

#eval List.map (α:=UInt8) UInt.bitcnt [
  0b0000, 0b0001, 0b0010, 0b0011, 0b0100, 0b0101, 0b0110, 0b0111,
  0b1000, 0b1001, 0b1010, 0b1011, 0b1100, 0b1101, 0b1110, 0b1111
]
