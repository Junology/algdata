/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Logic

import Algdata.Init.UInt

set_option autoImplicit false

/-!
# Quotient ring ℤ/256ℤ
-/

/--
The 8-bit unsigned integer type as the quotient ring ℤ/256ℤ.
-/
@[unbox]
structure ℤ256 : Type :=
  mk :: (val : UInt8) 
  deriving DecidableEq, Repr


namespace ℤ256

/-!
## Basic instances

@remark Since we will give `div`/`mod` later in terms of the 2-adic pseudo-norm, they do not appear in this section.
-/

@[inline]
protected
def toNat (x : ℤ256) : Nat := x.val.val.val

@[inline]
protected
def ofNat (n : @& Nat) : ℤ256 := mk (OfNat.ofNat n)

@[inline, match_pattern]
protected
abbrev zero : ℤ256 := mk UInt8.zero

@[inline, match_pattern]
protected
abbrev one : ℤ256 := mk UInt8.one

@[inline]
protected
def add (x y : ℤ256) : ℤ256 := mk (x.val + y.val)

@[inline]
protected
def sub (x y : ℤ256) : ℤ256 := mk (x.val - y.val)

@[inline]
protected
def neg (x : ℤ256) : ℤ256 := mk (0 - x.val)

@[inline]
protected
def mul (x y : ℤ256) : ℤ256 := mk (x.val * y.val)

/-- @remark `instOfNatNat` has priority 100. -/
instance (priority := 50) (n : Nat) : OfNat ℤ256 n := ⟨ℤ256.ofNat n⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0) := ⟨ℤ256.zero⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 1) := ⟨ℤ256.one⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 2) := ⟨mk (.raw 2 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 3) := ⟨mk (.raw 3 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 4) := ⟨mk (.raw 4 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 5) := ⟨mk (.raw 5 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 6) := ⟨mk (.raw 6 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 7) := ⟨mk (.raw 7 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 8) := ⟨mk (.raw 8 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0x10) := ⟨mk (.raw 0x10 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0x20) := ⟨mk (.raw 0x20 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0x40) := ⟨mk (.raw 0x40 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0x80) := ⟨mk (.raw 0x80 (by decide))⟩
instance (priority := 80) : OfNat ℤ256 (nat_lit 0xFF) := ⟨mk (.raw 0xFF 0xFF.lt_succ_self)⟩

instance : Add ℤ256 := ⟨ℤ256.add⟩
instance : Sub ℤ256 := ⟨ℤ256.sub⟩
instance : Neg ℤ256 := ⟨ℤ256.neg⟩
instance : Mul ℤ256 := ⟨ℤ256.mul⟩

@[inline]
protected
def toString (x : ℤ256) := x.val.binaryDigits

instance : ToString ℤ256 := ⟨ℤ256.toString⟩


/-!
## Bit operations

@remark For some of the operations, we provide two versions of implementations; one uses the corresponding operations on `UInt8` while the other avoid well-founded recursions. The equivalences of the two versions are proved in [Lemmas.lean](Algdata/Data/Z128/Lemmas.lean).
-/

@[inline]
protected
def complement (x : ℤ256) : ℤ256 := mk (~~~x.val)

/-- The (homogeneous) left shift operator. -/
@[inline]
protected
def shiftLeft (x y : ℤ256) : ℤ256 := mk (x.val <<< y.val)

/-- The (homogeneous) right shift operator. -/
@[inline]
protected
def shiftRight (x y : ℤ256) : ℤ256 := mk (x.val >>> y.val)

instance : Complement ℤ256 := ⟨ℤ256.complement⟩
instance : ShiftLeft ℤ256 := ⟨ℤ256.shiftLeft⟩
instance : ShiftRight ℤ256 := ⟨ℤ256.shiftRight⟩

/--
OR-operation: defined by `UInt8.lor`.
@warning As `UInt8.lor` uses well-founded recursion, do not try to reduce the function directly.
 -/
@[inline]
protected
def lor_wf (x y : ℤ256) : ℤ256 := mk (x.val ||| y.val)

/-- OR-operation: implemented without well-founded recursion. -/
@[implemented_by ℤ256.lor_wf]
protected
def lor (x y : ℤ256) : ℤ256 := aux (nat_lit 8) x y
  where
    aux : Nat → ℤ256 → ℤ256 → ℤ256
    | 0, _, _ => 0
    | n+1, x, y =>
      let z := aux n (x >>> 1) (y >>> 1)
      (z <<< 1) + mk (if x.val % 2 = 0 then y.val % 2 else 1)

/--
AND-operation: defined by `UInt8.land`.
@warning As `Uint8.land` uses well-founded recursion, do not try to reduce the function directly.
-/
@[inline]
protected
def land_wf (x y : ℤ256) : ℤ256 := mk (x.val &&& y.val)

/-- AND-operation: implemented without well-founded recursion. -/
@[implemented_by ℤ256.land_wf]
protected
def land (x y : ℤ256) : ℤ256 := aux (nat_lit 8) x y
  where
    aux : Nat → ℤ256 → ℤ256 → ℤ256
    | 0, _, _ => 0
    | n+1, x, y =>
      let z := aux n (x >>> 1) (y >>> 1)
      (z <<< 1) + mk (if x.val % 2 = 0 then 0 else y.val % 2)

/--
XOR-operation: defined by `UInt8.xor`.
@warning As `UInt8.xor` uses well-founded recursion, do not try to reduce the function directly.
-/
@[inline]
protected
def xor_wf (x y : ℤ256) : ℤ256 := mk (x.val ^^^ y.val)

/-- XOR-operation: implemented without well-founded recursion. -/
@[implemented_by ℤ256.xor_wf]
protected
def xor (x y : ℤ256) : ℤ256 := aux (nat_lit 8) x y
  where
    aux : Nat → ℤ256 → ℤ256 → ℤ256
    | 0, _, _ => 0
    | n+1, x, y =>
      let z := aux n (x >>> 1) (y >>> 1)
      (z <<< 1) + mk (if x.val % 2 = y.val % 2 then 0 else 1)

instance : AndOp ℤ256 := ⟨ℤ256.land⟩
instance : OrOp ℤ256 := ⟨ℤ256.lor⟩
instance : Xor ℤ256 := ⟨ℤ256.xor⟩

/--
Counting non-zero bits.
-/
@[inline]
def bitCount (x : ℤ256) : ℤ256 :=
  Id.run <| do
    let mut a := x
    a := (a &&& 0b01010101 : ℤ256) + (a &&& 0b10101010) >>> 1
    a := (a &&& 0b00110011 : ℤ256) + (a &&& 0b11001100) >>> 2
    a := (a &&& 0b00001111 : ℤ256) + (a &&& 0b11110000) >>> 4
    return a

/--
Given `x : ℤ256`, `x.tzmask` is the bit mask for trailing zeros; e.g.
```lean
tzmask 0b10110100 = 0b00000011
```
-/
@[inline]
def tzmask (x : ℤ256) : ℤ256 := ~~~x &&& (x-1)

/--
Count trailing zeros; e.g. `ℤ256.ctz 0b10110100 = 2`.
This function is exactly the *2-adic pseudo-norm*; for example, `x : ℤ256` is invertible if and only if `x.ctz = 0`.
-/
@[inline]
def ctz (x : ℤ256) : ℤ256 := x.tzmask.bitCount

@[inline]
def norm₂ (x : ℤ256) : Nat := x.ctz.toNat

/--
The position of the most significant bit; note that `n.toNat.log2 = n.msb.pred`.
```lean
-- []
#eval Nat.fold (λ n s => if (ℤ256.ofNat n).msb.pred = n.log2 then s else (n::s)) 256 []
```
-/
@[inline]
def msb (x : ℤ256) : ℤ256 :=
  Id.run <| do
    let mut a := x
    a := a ||| (a >>> 1)
    a := a ||| (a >>> 2)
    a := a ||| (a >>> 4)
    return a.bitCount


/-!
## Div/Mod

The quotient ring ℤ/256ℤ is an Euclidean ring in the sense that, given pair `x y : ℤ256`, there are unique elements `q r : ℤ256` such that

  - `x = q * y + r`
  - `r = 0 ∨ r.ctz < y.ctz`

Indeed, every element `x : ℤ256` is written in the form `x = u * 2^n` for `u : ℤ256` and `n : Nat` such that `u` is invertible and `n = x.norm₂`.
Moreover, such `r` is unique up to unit multiples of `y`.

Test code:
```lean
-- true
#eval let a := Array.ofFn (n:=UInt8.size) (λ n => mk ⟨n⟩); a.foldl (λ b x => b && a.foldl (λ b y => b && (x = (x / y) * y + x % y)) True) True
```
-/

/--
2-adic mod: `x % y` is the lower bits of `x` up to the `y.norm₂`-th bit.
Specifically, we have `x % 0 = x`.
-/
@[inline]
protected
def mod (x y : ℤ256) : ℤ256 := x &&& y.tzmask

/--
The 2-adic division (with 2-adic remainders).
@remark `x / 0 = 0`.
-/
@[inline]
protected
def div (x y : ℤ256) : ℤ256 :=
  if y = 0
  then 0
  else Id.run <| do
    let mut x := x >>> y.ctz
    let y := y >>> y.ctz
    let mut q := 0
    q := q ||| (x &&& 0x01); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| (x &&& 0x01) <<< 1; x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 2); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 3); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 4); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 5); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 6); x := (x - ((x &&& 0x01) * y)) >>> 1
    q := q ||| ((x &&& 0x01) <<< 7); x := (x - ((x &&& 0x01) * y)) >>> 1
    return q

instance : Mod ℤ256 := ⟨ℤ256.mod⟩
instance : Div ℤ256 := ⟨ℤ256.div⟩


/-!
## Recursors

As a truncated 2-adic integer, `ℤ256` has a recursor based on the 2-adic pseudo-norm.
-/

section recursor

private
theorem shiftRec_terminate_aux : ∀ (n : UInt8), n = 0 ∨ ((n >>> 1) < n)
| .zero => Or.inl rfl
| .raw (n+1) h => Or.inr $ by
  conv => change (n+1) / 2 % UInt8.size < n+1
  calc
    (n+1) / 2 % UInt8.size
      = (n+1) / 2 := Nat.mod_eq_of_lt (Trans.trans (Nat.div_le_self _ 2) h)
    _ < n+1 := Nat.div_lt_self n.zero_lt_succ (Nat.lt_succ_self 1)

protected
def shiftRec.{u} {motive : ℤ256 → Sort u} (zero : motive 0) (shift : (x : ℤ256) → x ≠ 0 → motive (x >>> 1) → motive x) : (x : ℤ256) → motive x
| 0 => zero
| mk (.raw (n+1) hn) =>
  have hneq : mk (UInt8.mk (Fin.mk (n+1) hn)) ≠ 0 := by intro h; cases h
  have : UInt8.mk (Fin.mk (n+1) hn) >>> 1 < UInt8.mk (Fin.mk (n+1) hn) :=
    Or.resolve_left (shiftRec_terminate_aux _) (by intro h; cases h)
  shift _ hneq (ℤ256.shiftRec zero shift ( mk (UInt8.mk (Fin.mk (n+1) hn) >>> 1)))
termination_by _ _ _ _ x => x.val.val.val

end recursor

end ℤ256
