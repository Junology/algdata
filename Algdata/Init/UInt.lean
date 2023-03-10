/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace UInt8

@[inline, match_pattern]
protected
abbrev zero : UInt8 := mk ⟨0, UInt8.size.pred.zero_lt_succ⟩

@[inline, match_pattern]
protected
abbrev one : UInt8 := mk ⟨1, Nat.succ_lt_succ UInt8.size.pred.pred.zero_lt_succ⟩

@[inline, match_pattern]
protected
abbrev raw (x : Nat) (h : x < UInt8.size) : UInt8 := mk ⟨x,h⟩

instance (priority := 80): OfNat UInt8 (nat_lit 0) := ⟨UInt8.zero⟩

instance (priority := 80): OfNat UInt8 (nat_lit 1) := ⟨UInt8.one⟩

protected
def pred : UInt8 → UInt8
| .zero => 0
| .raw (x+1) h => mk ⟨x, Nat.lt_of_succ_lt h⟩

protected
def pred2 : UInt8 → UInt8
| .zero => 0
| .one => 0
| .raw (x+2) h => mk ⟨x, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt h)⟩

protected
def binaryDigits (x : UInt8) (pre : String := "") : String :=
  pre ++ String.mk [
    if x &&& 0x80 = 0 then '0' else '1',
    if x &&& 0x40 = 0 then '0' else '1',
    if x &&& 0x20 = 0 then '0' else '1',
    if x &&& 0x10 = 0 then '0' else '1',
    if x &&& 0x08 = 0 then '0' else '1',
    if x &&& 0x04 = 0 then '0' else '1',
    if x &&& 0x02 = 0 then '0' else '1',
    if x &&& 0x01 = 0 then '0' else '1'
  ]

end UInt8
