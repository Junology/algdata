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

@[default_instance 200]
instance : OfNat UInt8 (nat_lit 0) := ⟨UInt8.zero⟩

@[default_instance 200]
instance : OfNat UInt8 (nat_lit 1) := ⟨UInt8.one⟩

protected
def pred : UInt8 → UInt8
| 0 => 0
| .raw (x+1) h => mk ⟨x, Nat.lt_of_succ_lt h⟩

protected
def pred2 : UInt8 → UInt8
| 0 => 0
| 1 => 0
| .raw (x+2) h => mk ⟨x, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt h)⟩

end UInt8
