/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Classes.UInt

/-!
# Truncated 2-adic integers

The unsigned integer types `UInt8`, `UInt16`, `UInt32`, and `UInt64` as well as `Bool` have arithmetic operators as in the quotient ring `ℤ/(2ⁿ)`, which we call the ***truncated 2-adic integer ring***.
From this point of view, these types have yet another mod/div operation other than the standard one; we call them ***2-adic mod/div***.
It turns out that `ℤ/(2ⁿ)` becomes a Euclid ring with non-trivial zero-factors.

In this file, we define a structure `UIntAdic2`; if `UInt α` (see [UInt.lean](../../Classes/UInt.lean)) and `∀ n, OfNat α n`, `UIntAdic2 α` essentially equals to `α` while its mod/div are 2-adic ones.
-/


@[unbox, specialize]
structure UIntAdic2 (α : Type) [(n : Nat) → OfNat α n] [UInt α] where
  val : α
  deriving DecidableEq, Repr


namespace UIntAdic2

variable {α : Type} [(n : Nat) → OfNat α n] [UInt α]

/-!
## Canonical maps from Nat/Int
-/

@[inline]
protected
def ofNat (n : Nat) : UIntAdic2 α := mk (OfNat.ofNat n)

@[inline]
protected
def ofInt : Int → UIntAdic2 α
| Int.ofNat n => UIntAdic2.ofNat n
| Int.negSucc n => mk (-OfNat.ofNat (α:=α) n - 1)

instance (n : Nat) : OfNat (UIntAdic2 α) n := ⟨UIntAdic2.ofNat n⟩
instance : Coe Int (UIntAdic2 α) := ⟨UIntAdic2.ofInt⟩


/-!
## Ring structure
-/

@[inline]
protected
abbrev add (x y : UIntAdic2 α) : UIntAdic2 α := mk (x.val + y.val)

@[inline]
protected
abbrev mul (x y : UIntAdic2 α) : UIntAdic2 α := mk (x.val * y.val)

@[inline]
protected
abbrev sub (x y : UIntAdic2 α) : UIntAdic2 α := mk (x.val - y.val)

@[inline]
protected
abbrev neg (x : UIntAdic2 α) : UIntAdic2 α := mk (-x.val)

@[inline]
instance : Add (UIntAdic2 α) := ⟨UIntAdic2.add⟩

@[inline]
instance : Mul (UIntAdic2 α) := ⟨UIntAdic2.mul⟩

@[inline]
instance : Sub (UIntAdic2 α) := ⟨UIntAdic2.sub⟩

@[inline]
instance : Neg (UIntAdic2 α) := ⟨UIntAdic2.neg⟩


/-!
## 2-adic division/modulus
-/

section DivMod

/-- 2-adic mod -/
@[inline]
def mod (x y : UIntAdic2 α) : UIntAdic2 α :=
  mk (x.val &&& (y.val ^^^ (y.val ||| (y.val - 1))))

/-- Check if `x` is invertible in the truncated 2-adic integer ring. Since the ring `ℤ/(2ⁿ)` is a local ring with residue field `ℤ/(2)`, an element is invertible if and only if its image in `ℤ/(2)` is `1`, or equivalently, the lowest bit of `x` is `True`. -/
@[inline]
def invertible (x : UIntAdic2 α) : Prop :=
  UInt.getBit x.val 0 = true

instance (x : UIntAdic2 α) : Decidable (x.invertible) :=
  inferInstanceAs (Decidable (UInt.getBit x.val 0 = true))

/--
2-adic reciprocal.

:::note warn
Even though the function is total, `x.recip` is an reciprocal of `x` only if `x` is invertible; i.e. `x.invertible = True`.
:::
-/
@[inline]
def recip (x : UIntAdic2 α) : UIntAdic2 α :=
  let rec @[specialize] loop (i : Nat) (a r : α) : α :=
    match i with
    | 0 => a
    | i+1 => loop i (a + r * a) (r * r)
  mk $ loop (Nat.log2' (UInt.length α)) 1 (1 - x.val)

@[inline]
def div [DecidableEq α] (x y : UIntAdic2 α) : UIntAdic2 α :=
  let n := UInt.ctz y.val
  ⟨x.val >>> n⟩ * recip ⟨y.val >>> n⟩

instance : Mod (UIntAdic2 α) :=
  ⟨mod⟩

instance [DecidableEq α] : Div (UIntAdic2 α) :=
  ⟨div⟩

end DivMod

end UIntAdic2
