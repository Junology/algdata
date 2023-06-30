/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

import Algdata.Init.Logic
import Algdata.Data.Nat.Rec

/-!
# Bit operations on Nat
-/

universe u v

namespace Nat

/-!
## Utility
-/

theorem eq_of_div_mod_two_eq {m n : Nat} (hdiv : m/2 = n/2) (hmod : m%2 = n%2) : m = n :=
  calc
    m = 2*(m/2) + m%2 := (Nat.div_add_mod m 2).symm
    _ = 2*(n/2) + n%2 := by rw [hdiv, hmod]
    _ = n := Nat.div_add_mod n 2

theorem eq_mod2_of_decide {m n : Nat} : decide (m%2 = 1) = decide (n%2 = 1) → m%2 = n%2 := by
  cases m.mod_two_eq_zero_or_one <;> cases n.mod_two_eq_zero_or_one
  <;> rw [‹m%2=_›, ‹n%2=_›] <;> intro hdec <;> cases hdec <;> rfl

/-!
## Accessing each bit
-/

/-- Get `i`-th bits of the binar representation of `Nat`. -/
def getBit (n : Nat) : Nat → Bool
| 0 => decide (n % 2 = 1)
| (i+1) => getBit (n/2) i

@[simp]
theorem zero_getBit : ∀ (i : Nat), Nat.zero.getBit i = false
| 0 => rfl
| (i+1) => zero_getBit i

theorem getBit_high {n k : Nat} : n < 2^k → ∀ i, i ≥ k → n.getBit i = false := by
  intro hn i hi
  induction k generalizing n i
  case zero => cases Nat.eq_zero_of_lt_one hn; exact zero_getBit i
  case succ k h_ind =>
    have : n/2 < 2^k := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).mpr hn
    cases hi
    case refl =>
      dsimp [getBit]
      exact h_ind ‹n/2 < 2^k› k Nat.le.refl
    case step i hstep =>
      dsimp [getBit]
      exact h_ind ‹n/2 < 2^k› i (Nat.le_of_succ_le hstep)

theorem getBit_two_pow (k i : Nat) : (2^k).getBit i = decide (k=i) := by
  induction i generalizing k
  case zero =>
    dsimp [getBit]
    cases k
    case zero => decide
    case succ k => conv => lhs; change decide (2^k*2%2 = 1); simp
  case succ i h_ind =>
    dsimp [getBit]
    cases k
    case zero =>
      conv => change getBit 0 i = false
      simp
    case succ k =>
      conv => lhs; arg 1; change 2^k*2/2; simp
      have : k = i ↔ k.succ = i.succ := ⟨λ h => h ▸ rfl, λ h => Nat.succ.inj h⟩
      rw [h_ind, decide_eq_decide_of_iff this]

theorem getBit_pred_two_pow (k i : Nat) : (2^k - 1).getBit i = decide (i < k) := by
  induction k generalizing i
  case zero =>
    conv => lhs; rw [Nat.pow_zero]; change getBit 0 i; rw [Nat.zero_getBit]
  case succ k h_ind =>
    cases i
    case zero =>
      dsimp [Nat.getBit]; apply decide_eq_decide_of_iff
      have := calc
        (2^k.succ - 1) % 2
          = (2^k*2 - 1) % 2 := by rw [Nat.pow_succ]
        _ = (2-1)%2 :=
          Nat.mul_sub_mod_right (Nat.pos_pow_of_pos (n:=2) _ (by decide)) (.step .refl)
        _ = 1 := rfl
      rw [this]
      constructor <;> intros; exact k.zero_lt_succ; rfl
    case succ i =>
      have := calc
        (2^k.succ - 1).getBit i.succ
          = ((2^k*2 - 1)/2).getBit i := by rw [Nat.pow_succ, Nat.getBit]
        _ = (2^k - 1).getBit i :=
          by rw [Nat.mul_comm, Nat.mul_sub_div 0 2 (2^k) (Nat.pos_mul_of_pos (by decide) (Nat.pos_pow_of_pos (n:=2) k (by decide)))]; rfl
      rw [this, h_ind]; apply decide_eq_decide_of_iff
      exact ⟨Nat.succ_lt_succ, Nat.lt_of_succ_lt_succ⟩

theorem getBit_mod_two_pow (n k i : Nat) : (n % 2^k).getBit i = (decide (i < k) && n.getBit i) := by
  induction i generalizing n k
  case zero =>
    cases k
    case zero => conv => lhs; rw [Nat.pow_zero, Nat.mod_one, Nat.zero_getBit]
    case succ k =>
      conv => lhs; change decide (n%(2^k*2)%2=1); rw [Nat.mod_mul_mod_right]
      conv => rhs; simp [decide_eq_true k.zero_lt_succ]
  case succ i h_ind =>
    cases k
    case zero => conv => lhs; rw [Nat.pow_zero, Nat.mod_one, Nat.zero_getBit]
    case succ k =>
      unfold getBit
      have : i.succ < k.succ ↔ i < k :=
        ⟨λ h => Nat.lt_of_succ_lt_succ h, λ h => Nat.succ_lt_succ h⟩
      rw [decide_eq_decide_of_iff this]
      conv => lhs; arg 1; change n%(2^k*2)/2; rw [Nat.mul_comm, Nat.mod_mul_div_left]
      exact h_ind (n/2) k

theorem eq_zero_of_getBit {n : Nat} (h : ∀ i, n.getBit i = false) : n = 0 := by
  cases n.eq_zero_or_pos
  case inl hzero => exact hzero
  case inr hpos =>
    have : n/2 < n := Nat.div_lt_self hpos (Nat.lt_succ_self 1)
    have : n/2 = 0 := eq_zero_of_getBit (n:=n/2) (λ i => h i.succ)
    have : n%2 = 0 := eq_mod2_of_decide (n:=0) (h 0)
    exact eq_of_div_mod_two_eq (n:=0) ‹n/2=0› ‹n%2=0›

theorem bitext {m n : Nat} : (∀ i, m.getBit i = n.getBit i) → m = n := by
  intro h
  have : m % 2 = n % 2 := eq_mod2_of_decide $ h 0
  have : m / 2 = n / 2 := by
    cases m.eq_zero_or_pos
    case inl hm => 
      cases hm; apply Eq.symm
      apply eq_zero_of_getBit
      exact λ i => zero_getBit i.succ ▸ (h i.succ).symm
    case inr hm =>
      have : m/2 < m := Nat.div_lt_self hm (Nat.lt_succ_self 1)
      exact bitext (m:=m/2) (n:=n/2) (λ i => h i.succ)
  exact eq_of_div_mod_two_eq ‹_› ‹_›


/-!
## Bitwise operations
-/

theorem bitwise_div_two (f : Bool → Bool → Bool) (m n : Nat) : bitwise f m n / 2 = bitwise f (m/2) (n/2) := by
  by_cases m = 0
  case pos hm =>
    cases hm; unfold bitwise; simp
    cases hfft : f false true <;> simp [hfft]
  case neg hm =>
    by_cases n = 0
    case pos hn =>
      cases hn
      unfold bitwise; simp; simp [if_neg hm]
      cases hftf : f true false <;> by_cases hm2 : m / 2 = 0 <;> simp [hftf, hm2]
    case neg hn =>
      conv => lhs; unfold bitwise; simp [if_neg hm, if_neg hn]
      simp [app_ite (·/2), ←Nat.mul_two]
      rw [Nat.add_comm, Nat.add_mul_div_right 1 _ (z:=2) (Nat.zero_lt_succ 1)]
      have : 1/2 = 0 := by decide
      rw [this, Nat.zero_add]
      simp

theorem bitwise_mod_two (f : Bool → Bool → Bool) (f_stable : f false false = false) (m n : Nat) : bitwise f m n % 2 = if f (decide (m%2 = 1)) (decide (n%2 = 1)) then 1 else 0 := by
  by_cases m = 0
  case pos hm =>
    cases hm; unfold bitwise; simp
    cases hfft : f false true
    case false =>
      have : ∀ b, f false b = false := λ b => by cases b; exact f_stable; exact hfft
      simp [this]
    case true =>
      have : ∀ b, f false b = b := λ b => by cases b; exact f_stable; exact hfft
      simp [this]
      apply (n.mod_two_eq_zero_or_one).elim <;> intro h <;> simp [h]
  case neg hm =>
    unfold bitwise
    simp [if_neg hm, app_ite (·%2), ←Nat.mul_two, Nat.add_mod]
    by_cases n = 0
    case pos hn =>
      cases hn; simp
      cases hftf : f true false
      case true =>
        have : ∀ b, f b false = b := λ b => by cases b; exact f_stable; exact hftf
        simp [this]
        apply m.mod_two_eq_zero_or_one.elim <;> intro h <;> simp [h]
      case false =>
        have : ∀ b, f b false = false := λ b => by cases b; exact f_stable; exact hftf
        simp [this]
    case neg hn =>
      rw [if_neg hn]
      rfl

theorem bitwise_lt_exp2 (f : Bool → Bool → Bool) {m n k : Nat} (hmk : m < 2^k) (hnk : n < 2^k) : bitwise f m n < 2^k := by
  induction k generalizing m n
  case zero =>
    cases m.eq_zero_of_lt_one hmk; cases n.eq_zero_of_lt_one hnk
    unfold bitwise; simp
  case succ k h_ind =>
    by_cases m = 0
    case pos hm =>
      cases hm
      unfold bitwise; simp
      cases f false true <;> simp
      . exact Nat.pos_pow_of_pos k.succ (Nat.zero_lt_succ 1)
      . exact hnk
    case neg hm =>
      by_cases n = 0
      case pos hn =>
        cases hn
        unfold bitwise; simp [hm]
        cases f true false <;> simp
        . exact Nat.pos_pow_of_pos k.succ (Nat.zero_lt_succ 1)
        . exact hmk
      case neg hn =>
        unfold bitwise; simp [hm, hn]
        rw [←Nat.mul_two, Nat.pow_succ]
        have : m/2 < 2^k := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).mpr hmk
        have : n/2 < 2^k := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 1)).mpr hnk
        cases f (m%2=1) (n%2=1) <;> simp
        . apply Nat.mul_lt_mul_of_pos_right ?_ (Nat.zero_lt_succ 1)
          exact h_ind ‹_› ‹_›
        . calc
          bitwise f (m/2) (n/2) * 2 + 1 
            < bitwise f (m/2) (n/2) * 2 + 2 := Nat.lt_succ_self _
          _ = (bitwise f (m/2) (n/2)) * 2 + 1*2 := rfl
          _ = (bitwise f (m/2) (n/2) + 1) * 2 := (Nat.add_mul _ _ 2).symm
          _ ≤ 2^k * 2 := Nat.mul_le_mul_right 2 (h_ind ‹m/2 < 2^k› ‹n/2 < 2^k›)

theorem bitwise_getBit (f : Bool → Bool → Bool) (f_stable : f false false = false) (m n : Nat) : ∀ i, (bitwise f m n).getBit i = f (m.getBit i) (n.getBit i) := by
  intro i
  induction i generalizing m n
  case zero =>
    by_cases m = 0
    case pos hm =>
      cases hm; simp
      unfold bitwise; simp
      cases hft : f false true
      case false =>
        have : ∀ b, f false b = false := by intro b; cases b <;> assumption
        simp [this]
      case true =>
        have : ∀ b, f false b = b := by intro b; cases b <;> assumption
        simp [this]
    case neg hm =>
      unfold bitwise; simp [if_neg hm]
      by_cases n = 0
      case pos hn =>
        cases hn; simp
        cases htf : f true false
        case false =>
          have : ∀ b, f b false = false := by intro b; cases b <;> assumption
          simp [this]
        case true =>
          have : ∀ b, f b false = b := by intro b; cases b <;> assumption
          simp [this]
      case neg hn =>
        simp [if_neg hn]
        rw [app_ite (Nat.getBit · 0), ←Nat.mul_two, Nat.add_comm]
        dsimp [getBit]
        cases hf : f (decide (m%2 = 1)) (decide (n%2 = 1)) <;> simp [hf]
  case succ i h_ind =>
    dsimp [getBit]; rw [bitwise_div_two, h_ind]

theorem bitwise_mod_two_pow (f : Bool → Bool → Bool) (f_stable : f false false = false) (m n k : Nat) : bitwise f m n % 2^k = bitwise f (m%2^k) (n%2^k) := by
  apply bitext; intro i
  simp [getBit_mod_two_pow, bitwise_getBit f f_stable]
  cases decide (i<k) <;> simp [f_stable]

theorem bitwise_idempotent {f : Bool → Bool → Bool} (h : ∀ b, f b b = b) (n : Nat) : bitwise f n n = n := by
  apply Nat.bitext; intro i
  simp [Nat.bitwise_getBit f (h false), h]

theorem bitwise_nilpotent {f : Bool → Bool → Bool} (h : ∀ b, f b b = false) (n : Nat) : bitwise f n n = 0 := by
  apply Nat.bitext; intro i
  simp [Nat.bitwise_getBit f (h false), h]

theorem bitwise_assoc {f : Bool → Bool → Bool} (f_stable : f false false = false) (h : ∀ a b c, f (f a b) c = f a (f b c)) (l m n : Nat) : bitwise f (bitwise f l m) n = bitwise f l (bitwise f m n) := by
  apply Nat.bitext; intro i
  simp [Nat.bitwise_getBit f f_stable, h]

theorem bitwise_flip {f : Bool → Bool → Bool} : ∀ {m n}, bitwise (flip f) m n = bitwise f n m := by
  intro m n
  by_cases m = 0
  case pos hm =>
    cases hm
    unfold bitwise
    simp [flip]
    by_cases n = 0
    case pos hn =>
      cases hn; rw [if_pos (Eq.refl 0)]
      by_cases f true false <;> simp
    case neg hn => rw [if_neg hn]
  case neg hm =>
    unfold bitwise
    rw [if_neg hm, if_neg hm]
    dsimp
    have : m > 0 := Nat.pos_of_ne_zero hm
    have : m/2 < m := Nat.div_lt_self ‹m>0› (Nat.lt_succ_self 1)
    rw [bitwise_flip (m:=m/2) (n:=n/2)]
    rfl

theorem bitwise_comm {f : Bool → Bool → Bool} (h : ∀ a b, f a b = f b a) : ∀ {m n}, bitwise f m n = bitwise f n m := by
  have : flip f = f := funext (λ a => funext (λ b => h b a))
  intro m n
  rw [←bitwise_flip (m:=m) (n:=n), this]

/-!
### `Nat.lor`
-/

/-- `Nat.lor` is idempotent. -/
@[simp]
protected
theorem lor_self (n : Nat) : n ||| n = n :=
  bitwise_idempotent (n:=n) Bool.or_self

/-- `Nat.lor` is commutative. -/
protected
theorem lor_comm (m n : Nat) : m ||| n = n ||| m :=
  bitwise_comm (λ a b => by cases a <;> cases b <;> decide)

/-- `Nat.lor` is associative. -/
protected
theorem lor_assoc (l m n : Nat) : l ||| m ||| n = l ||| (m ||| n) :=
  bitwise_assoc (by decide) Bool.or_assoc l m n

@[simp]
protected
theorem lor_zero (n : Nat) : n ||| 0 = n := by
  apply bitext
  intro i
  conv =>
    change (bitwise or n 0).getBit i = n.getBit i
    rw [bitwise_getBit, zero_getBit, Bool.or_false]

@[simp]
protected
theorem zero_lor (n : Nat) : 0 ||| n = n := by
  rw [Nat.lor_comm, Nat.lor_zero]

protected
theorem lor_getBit (m n i : Nat) : (m ||| n).getBit i = (m.getBit i || n.getBit i) := by
  conv => lhs; change (bitwise or m n).getBit i; rw [bitwise_getBit]


/-!
### `Nat.land`
-/

@[simp]
protected
theorem land_self (n : Nat) : n &&& n = n :=
  bitwise_idempotent (n:=n) Bool.and_self

protected
theorem land_comm (m n : Nat) : m &&& n = n &&& m :=
  bitwise_comm (λ a b => by cases a <;> cases b <;> decide)

protected
theorem land_assoc (l m n : Nat) : l &&& m &&& n = l &&& (m &&& n) :=
  bitwise_assoc (by decide) Bool.and_assoc l m n

@[simp]
protected
theorem land_zero (n : Nat) : n &&& 0 = 0 := by
  apply bitext
  intro i
  conv =>
    change (bitwise and n 0).getBit i = getBit 0 i
    rw [bitwise_getBit, zero_getBit, Bool.and_false]

@[simp]
protected
theorem zero_land (n : Nat) : 0 &&& n = 0 := by
  rw [Nat.land_comm, Nat.land_zero]

protected
theorem land_exp2_sub_one (k : Nat) : ∀ n, n &&& (2^k - 1) = n % (2^k) := by
  intro n
  induction k generalizing n
  case zero => calc
    n &&& 2^0 - 1 = n &&& 0 := rfl
    _             = 0 := Nat.land_zero n
    _             = n % 1 := n.mod_one.symm
    _             = n % 2^0 := rfl
  case succ k h_ind =>
    conv =>
      change bitwise and n (2^k*2 - 1) = n % (2^k*2)
      rw [Nat.mul_comm _ 2]
    apply eq_of_div_mod_two_eq
    . rw [bitwise_div_two]
      rw [Nat.mul_sub_div 0 2 (2^k) (by rw [Nat.mul_comm]; exact Nat.pos_pow_of_pos (n:=2) (k+1) (by decide))]
      rw [Nat.mod_mul_div_left n 2 (2^k)]
      exact h_ind (n/2)
    . rw [bitwise_mod_two and (by decide)]
      simp
      have : ∀ (l : Nat), l > 0 → (2*l - 1) % 2 = 1 := by
        intro l hl
        cases l
        case zero => cases hl
        case succ l =>
          conv =>
            lhs; rw [Nat.mul_succ]; change (2*l+1+1-1)%2
            rw [Nat.add_sub_cancel, Nat.add_comm, Nat.add_mul_mod_self_left]
      simp [this (2^k) (Nat.pos_pow_of_pos k (by decide))]
      rw [Nat.mod_mul_mod_left n 2 _]
      apply (n.mod_two_eq_zero_or_one).elim <;> intro h <;> simp [h]

protected
theorem land_getBit (m n i : Nat) : (m &&& n).getBit i = (m.getBit i && n.getBit i) := by
  conv => lhs; change (bitwise and m n).getBit i; rw [bitwise_getBit]

@[simp]
theorem land_one : ∀ (n : Nat), n &&& 1 = n % 2 := Nat.land_exp2_sub_one 1
@[simp]
theorem land_F : ∀ (n : Nat), n &&& 0xF = n % 0x10 := Nat.land_exp2_sub_one 4
@[simp]
theorem land_FF : ∀ (n : Nat), n &&& 0xFF = n % 0x100 := Nat.land_exp2_sub_one 8
@[simp]
theorem land_FFFF : ∀ (n : Nat), n &&& 0xFFFF = n % 0x10000 := Nat.land_exp2_sub_one 16


/-!
### `Nat.xor`
-/

@[simp]
protected
theorem xor_self (n : Nat) : n ^^^ n = 0 :=
  bitwise_nilpotent (λ b => by cases b <;> decide) n

protected
theorem xor_comm (m n : Nat) : m ^^^ n = n ^^^ m :=
  bitwise_comm (λ a b => by cases a <;> cases b <;> decide)

protected
theorem xor_assoc (l m n : Nat) : l ^^^ m ^^^ n = l ^^^ (m ^^^ n) :=
  bitwise_assoc (by decide) (λ a b c => by cases a <;> cases b <;> cases c <;> decide) l m n

@[simp]
protected
theorem xor_zero (n : Nat) : n ^^^ 0 = n := by
  apply bitext; intro i
  conv =>
    change (bitwise bne n 0).getBit i = n.getBit i
    rw [Nat.bitwise_getBit, Nat.zero_getBit]
  cases n.getBit i <;> decide

@[simp]
protected
theorem zero_xor (n : Nat) : 0 ^^^ n = n := by
  rw [Nat.xor_comm, Nat.xor_zero]

protected
theorem even_xor_one {n : Nat} : n % 2 = 0 → n ^^^ 1 = n + 1 := by
  intro heven
  by_cases n = 0
  case pos h => cases h; decide
  case neg h =>
    conv =>
      lhs; change bitwise bne n 1
      unfold bitwise; simp [h, heven]
      change (n/2 ^^^ 0) + (n/2 ^^^ 0) + 1
      rw [Nat.xor_zero, ←Nat.mul_two, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]

protected
theorem odd_xor_one {n : Nat} : n % 2 = 1 → n ^^^ 1 = n - 1 := by
  intro hodd
  have : n ≠ 0 := λ h => by cases h; cases hodd
  conv =>
    lhs; change bitwise bne n 1
    unfold bitwise; simp [this, hodd]
    change (n/2 ^^^ 0) + (n/2 ^^^ 0)
    rw [Nat.xor_zero, ←Nat.mul_two]
  conv =>
    rhs; rw [←Nat.div_add_mod n 2, hodd, Nat.add_sub_cancel, Nat.mul_comm]

protected
theorem xor_one (n : Nat) : n ^^^ 1 = if n % 2 = 1 then n-1 else n+1 := by
  cases n.mod_two_eq_zero_or_one
  case inl h => simp [h, n.even_xor_one h]
  case inr h => simp [h, n.odd_xor_one h]

protected
theorem xor_getBit (m n i : Nat) : (m ^^^ n).getBit i = (m.getBit i != n.getBit i) := by
  conv => lhs; change (bitwise bne m n).getBit i; rw [bitwise_getBit]


/-!
### Distributive laws
-/

protected
theorem lor_land (l m n : Nat) : (l ||| m) &&& n = (l &&& n) ||| (m &&& n) := by
  apply bitext; intro i
  simp [Nat.lor_getBit, Nat.land_getBit]
  cases l.getBit i <;> cases m.getBit i <;> cases n.getBit i <;> decide

protected
theorem land_lor (l m n : Nat) : l &&& (m ||| n) = (l &&& m) ||| (l &&& n) := by
  apply bitext; intro i
  simp [Nat.lor_getBit, Nat.land_getBit]
  cases l.getBit i <;> cases m.getBit i <;> cases n.getBit i <;> decide

@[simp]
protected
theorem xor_and (l m n : Nat) : (l ^^^ m) &&& n = (l &&& n) ^^^ (m &&& n) := by
  apply bitext; intro i
  conv => lhs; change (bitwise and (bitwise bne l m) n).getBit i
  conv => rhs; change (bitwise bne (bitwise and l n) (bitwise and m n)).getBit i
  simp [bitwise_getBit]
  cases l.getBit i <;> cases m.getBit i <;> cases n.getBit i <;> decide

@[simp]
protected
theorem and_xor (l m n : Nat) : l &&& (m ^^^ n) = (l &&& m) ^^^ (l &&& n) := by
  apply bitext; intro i
  conv => lhs; change (bitwise and l (bitwise bne m n)).getBit i
  conv => rhs; change (bitwise bne (bitwise and l m) (bitwise and l n)).getBit i
  simp [bitwise_getBit]
  cases l.getBit i <;> cases m.getBit i <;> cases n.getBit i <;> decide

@[simp]
protected
theorem lor_mod_two_pow (m n k : Nat) : (m ||| n) % 2^k = (m%2^k) ||| (n%2^k) :=
  bitwise_mod_two_pow or (by decide) m n k

@[simp]
protected
theorem land_mod_two_pow (m n k : Nat) : (m &&& n) % 2^k = (m%2^k) &&& (n%2^k) :=
  bitwise_mod_two_pow and (by decide) m n k

@[simp]
protected
theorem xor_mod_two_pow (m n k : Nat) : (m ^^^ n) % 2^k = (m%2^k) ^^^ (n%2^k) :=
  bitwise_mod_two_pow bne (by decide) m n k


/-!
## Bit shifts
-/

@[simp]
theorem shiftLeft_zero (n : Nat) : n <<< 0 = n := rfl

@[simp]
theorem shiftLeft_succ (n k : Nat) : n <<< k.succ = 2 * (n <<< k) := by
  simp; rw [←Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm 2]; rfl

@[simp]
theorem shiftLeft_one (n : Nat) : n <<< 1 = 2*n := rfl

@[simp]
theorem shiftLeft_shiftLeft (n k l : Nat) : (n <<< k) <<< l = n <<< (k+l) := by
  induction l
  case zero => rfl
  case succ l h_ind =>
    conv =>
      rw [add_succ, shiftLeft_succ, shiftLeft_succ, h_ind]

@[simp]
theorem shiftRight_zero (n : Nat) : n >>> 0 = n := rfl

@[simp]
theorem shiftRight_succ (n k : Nat) : n >>> k.succ = (n >>> k) / 2 := rfl

@[simp]
theorem shiftRight_shiftRight (n k l : Nat) : (n >>> k) >>> l = n >>> (k+l) := by
  induction l
  case zero => rfl
  case succ l h_ind =>
    conv =>
      rw [add_succ, shiftRight_succ, shiftRight_succ, h_ind]

@[simp]
theorem zero_shiftLeft (k : Nat) : 0 <<< k = 0 := by simp

@[simp]
theorem zero_shiftRight (k : Nat) : 0 >>> k = 0 := by
  induction k
  case zero => rfl
  case succ k h_ind => rw [shiftRight_succ, h_ind]; rfl

@[simp]
theorem shiftLeft_shiftRight_self (n k : Nat) : (n <<< k) >>> k  = n := by
  induction k generalizing n
  case zero => rfl
  case succ k h_ind =>
    conv =>
      lhs; simp; change (n * (2^k*2)) >>> k / 2
      rw [Nat.mul_comm (2^k) 2, ←Nat.mul_assoc]
      rw [←Nat.shiftLeft_eq (n*2) k, h_ind (n*2), Nat.mul_div_cancel n (n:=2) (by decide)]

theorem shiftLeft_getBit_lt (n k : Nat) {i : Nat} : i < k → (n <<< k).getBit i = false := by
  intro h
  induction i generalizing n k
  case zero =>
    have : k.pred.succ = k := Nat.succ_pred_eq_of_pos h
    rw [←this, Nat.shiftLeft_succ]
    conv => lhs; change decide ((2*n <<< k.pred) % 2 = 1); simp
  case succ i h_ind =>
    have : k.pred.succ = k := Nat.succ_pred_eq_of_pos (trans i.zero_lt_succ h)
    rw [←this, Nat.shiftLeft_succ]
    conv =>
      lhs; change getBit ((2 * n <<< k.pred) / 2) i
      rw [Nat.mul_div_cancel_left _ (Nat.zero_lt_succ 1)]
    apply h_ind
    exact Nat.lt_of_succ_lt_succ (trans h this.symm)

theorem shiftLeft_getBit_ge (n k : Nat) {i : Nat} : i ≥ k → (n <<< k).getBit i = n.getBit (i-k) := by
  intro h
  induction k generalizing n i
  case zero => rfl
  case succ k h_ind =>
    have : i-k = (i-k.succ).succ := by
      rw [Nat.sub_succ i k]
      apply (Nat.succ_pred_eq_of_pos ?_).symm
      exact Nat.zero_lt_sub_of_lt h
    conv =>
      lhs; change (n <<< (k+1)).getBit i
      rw [Nat.add_comm, ←Nat.shiftLeft_shiftLeft]
      rw [h_ind (n <<< 1) (Nat.le_of_succ_le h), this]
      change ((2*n)/2).getBit (i-k.succ)
      simp

theorem shiftLeft_getBit (n k i : Nat) : (n <<< k).getBit i = (i ≥ k && n.getBit (i-k)) := by
  cases Nat.lt_or_ge i k
  case inl hlt =>
    rw [decide_eq_false (Nat.not_le_of_gt hlt), Bool.false_and]
    exact shiftLeft_getBit_lt n k hlt
  case inr hge =>
    rw [decide_eq_true hge, Bool.true_and]
    exact shiftLeft_getBit_ge n k hge

@[simp]
theorem shiftRight_getBit (n k i : Nat) : (n >>> k).getBit i = n.getBit (i+k) := by
  induction k generalizing n i
  case zero => rfl
  case succ k h_ind =>
    conv =>
      lhs; rw [Nat.succ_eq_add_one, Nat.add_comm, ←Nat.shiftRight_shiftRight]
      rw [h_ind]

@[simp]
theorem bitwise_shiftLeft (f : Bool → Bool → Bool) (f_stable : f false false = false) (m n k : Nat) : bitwise f m n <<< k = bitwise f (m <<< k) (n <<< k) := by
  apply bitext; intro i; simp only [shiftLeft_getBit, bitwise_getBit f f_stable]
  cases decide (i ≥ k) <;> simp [f_stable]

@[simp]
theorem lor_shiftLeft (m n k : Nat) : (m ||| n) <<< k = m <<< k ||| n <<< k :=
  bitwise_shiftLeft or (by decide) m n k

@[simp]
theorem land_shiftLeft (m n k : Nat) : (m &&& n) <<< k = m <<< k &&& n <<< k :=
  bitwise_shiftLeft and (by decide) m n k

@[simp]
theorem xor_shiftLeft (m n k : Nat) : (m ^^^ n) <<< k = m <<< k ^^^ n <<< k :=
  bitwise_shiftLeft bne (by decide) m n k

@[simp]
theorem bitwise_shiftRight (f : Bool → Bool → Bool) (f_stable : f false false = false) (m n k : Nat) : (bitwise f m n) >>> k = bitwise f (m >>> k) (n >>> k) := by
  apply bitext; intro i; simp [bitwise_getBit f f_stable]

@[simp]
theorem lor_shiftRight (m n k : Nat) : (m ||| n) >>> k = ((m >>> k) ||| (n >>> k)) :=
  bitwise_shiftRight or (by decide) m n k

@[simp]
theorem land_shiftRight (m n k : Nat) : (m &&& n) >>> k = ((m >>> k) &&& (n >>> k)) :=
  bitwise_shiftRight and (by decide) m n k

@[simp]
theorem xor_shiftRight (m n k : Nat) : (m ^^^ n) >>> k = ((m >>> k) ^^^ (n >>> k)) :=
  bitwise_shiftRight bne (by decide) m n k


/-!
## Arithmetic operators in terms of bit operators
-/

theorem succ_eq_xor_add_land_shiftLeft (n : Nat) : n.succ = (n ^^^ 1) + ((n &&& 1) <<< 1) := by
  cases n.mod_two_eq_zero_or_one
  case inl h => simp [Nat.even_xor_one h, h]
  case inr h =>
    simp [Nat.odd_xor_one h, h]
    cases n
    case zero => cases h
    case succ n => rfl

theorem add_getBit_zero (m n : Nat) : (m+n).getBit 0 = (m ^^^ n).getBit 0 := by
  conv =>
    rhs; change (bitwise bne m n).getBit 0
    rw [bitwise_getBit bne (by decide)]
  unfold getBit
  rw [Nat.add_mod m n 2]
  apply m.mod_two_eq_zero_or_one.elim
  <;> apply n.mod_two_eq_zero_or_one.elim
  <;> (intro hn hm; rw [hn, hm]; decide)

theorem add_div_two (m n : Nat) : (m+n) / 2 = m/2 + n/2 + if (m &&& n).getBit 0 then 1 else 0 := by
  conv =>
    lhs; rw [←m.div_add_mod 2, ←n.div_add_mod 2]
    rw [←Nat.add_assoc, Nat.add_assoc _ (m%2), Nat.add_comm (m%2), ←Nat.add_assoc]
    rw [←Nat.mul_add 2, Nat.add_assoc, Nat.mul_add_div_left (x:=2) (y:=m/2+n/2) (z:=m%2+n%2) (by decide)]
  apply congrArg
  conv =>
    rhs; change if (bitwise and m n).getBit 0 = true then 1 else 0
    rw [bitwise_getBit and (by decide)]
  unfold getBit
  apply m.mod_two_eq_zero_or_one.elim <;> apply n.mod_two_eq_zero_or_one.elim
  <;> (intro hn hm; rw [hn, hm]; decide)

theorem add_eq_xor {m n : Nat} (disjoint : m &&& n = 0) : m + n = m ^^^ n := by
  apply (Nat.eq_zero_or_pos m).elim; (intro hm; cases hm; simp)
  intro hm
  apply eq_of_div_mod_two_eq
  . have : (m &&& n).getBit 0 = false := by simp [disjoint]
    conv => lhs; simp [add_div_two, this]; change (m >>> 1) + (n >>> 1)
    conv => rhs; change (m ^^^ n) >>> 1; rw [xor_shiftRight]
    have : m >>> 1 < m := Nat.div_lt_self hm (Nat.lt_succ_self 1)
    exact add_eq_xor (m:=m >>> 1) (n:=n >>> 1) (by rw [←land_shiftRight, disjoint]; rfl)
  . exact eq_mod2_of_decide (add_getBit_zero m n)

theorem sub_eq_xor {m n : Nat} (incl : m &&& n = n) : m - n = m ^^^ n := by
  apply Nat.sub_eq_of_eq_add
  have := calc
    (m ^^^ n) &&& n
      = (m &&& n) ^^^ (n &&& n) := Nat.xor_and m n n
    _ = n ^^^ n := by rw [incl, Nat.land_self n]
    _ = 0 := Nat.xor_self n
  simp [add_eq_xor this, Nat.xor_assoc]

theorem bitdivide (n k : Nat) : n = (n ^^^ (n &&& k)) + (n &&& k) := by
  have : (n ^^^ (n &&& k)) &&& (n &&& k) = 0 := by
    simp [←Nat.land_assoc n n k]
  conv =>
    rhs; simp [add_eq_xor this, Nat.xor_assoc]

theorem setminus_land_setminus (m n : Nat) : (m ^^^ (m &&& n)) &&& (n ^^^ (m &&& n)) = 0 := by
  simp [Nat.land_assoc m n n, ←Nat.land_assoc m m n]

theorem setminus_add_setminus (m n : Nat) : (m ^^^ (m &&& n)) + (n ^^^ (m &&& n)) = m ^^^ n := by
  rw [add_eq_xor (setminus_land_setminus m n)]
  rw [Nat.xor_assoc, ←Nat.xor_assoc (m &&& n), Nat.xor_comm (m &&& n), Nat.xor_assoc]
  simp

theorem add_eq_xor_add_carry (m n : Nat) : m + n = (m ^^^ n) + ((m &&& n) <<< 1) := by
  conv =>
    lhs; congr
    . rw [bitdivide m n]
    . rw [bitdivide n m]
  conv =>
    lhs; rw [Nat.land_comm n m]
    rw [Nat.add_assoc, ←Nat.add_assoc (m &&& n), Nat.add_comm (m &&& n), Nat.add_assoc]
    rw [←Nat.two_mul, ←Nat.add_assoc]
    change (m ^^^ (m &&& n)) + (n ^^^ (m &&& n)) + ((m &&& n) <<< 1)
    rw [setminus_add_setminus]


/-!
## The least significant bit
-/

protected
def lsb (n : Nat) : Nat := n ^^^ (n &&& (n-1))

@[simp]
protected
theorem lsb_zero : Nat.lsb 0 = 0 := rfl

protected
theorem lsb_of_odd {n : Nat} : n % 2 = 1 → n.lsb = 1 := by
  intro h
  unfold Nat.lsb
  have : n = 2*(n/2) + 1 :=
    Eq.symm $ Nat.add_comm .. ▸ h ▸ Nat.mod_add_div n 2
  clear h; rw [this, Nat.add_sub_cancel]
  have : 2*(n/2) + 1 = 2*(n/2) ^^^ 1 := by
    apply Nat.add_eq_xor
    rw [Nat.land_one, Nat.mul_mod_right]
  simp only [this]
  rw [Nat.xor_and, Nat.land_self]
  rw [←Nat.xor_assoc, Nat.xor_comm _ 1, Nat.xor_assoc 1, Nat.xor_self, Nat.xor_zero]
  have : ∀ k, 1 &&& 2 * k = 0 := by
    intro k; rw [Nat.land_comm, Nat.land_one, Nat.mul_mod_right]
  rw [this, Nat.xor_zero]

protected
theorem lsb_shiftLeft : ∀ (n k : Nat), n.lsb <<< k = (n <<< k).lsb := by
  suffices ∀ n, 2*n.lsb = (2*n).lsb by
    intro n k
    induction k generalizing n
    case zero => rfl
    case succ k h_ind =>
      simp only [Nat.succ_eq_add_one, ←Nat.shiftLeft_shiftLeft, h_ind]
      conv => change 2*(n <<< k).lsb = (2* (n <<< k)).lsb
      rw [this]
  intro n
  cases n
  case zero => rfl
  case succ n =>
    unfold Nat.lsb
    have : 2 * n.succ - 1 = 2 * (n.succ - 1) + 1 := by
      simp only [Nat.mul_succ, Nat.succ_sub_one]
    have : ∀ (k l : Nat), (2*k) &&& (2*l + 1) = 2*k &&& 2*l := by
      intro k l
      have : ∀ m, 2*m &&& 1 = 0 := by intros; rw [Nat.land_one, Nat.mul_mod_right]
      have : 2*l + 1 = 2*l ^^^ 1 := Nat.add_eq_xor (this l)
      calc
        2*k &&& (2*l + 1)
          = 2*k &&& (2*l ^^^ 1) := by rw [‹2*l + 1 = 2*l ^^^ 1›]
        _ = (2*k &&& 2*l) ^^^ (2*k &&& 1) := Nat.and_xor ..
        _ = (2*k &&& 2*l) ^^^ 0 := by rw [‹∀ m, 2*m &&& 1 = 0›]
        _ = 2*k &&& 2 * l:= by rw [Nat.xor_zero]
    rw [‹2*n.succ - 1 = 2 * (n.succ - 1) + 1›, this]
    conv =>
      rhs; simp only [←Nat.shiftLeft_one]
      simp only [←Nat.land_shiftLeft, ←Nat.xor_shiftLeft]

protected
theorem lsb_of_even {n : Nat} : n % 2 = 0 → n.lsb = (n/2).lsb <<< 1 := by
  intro heven
  have hn : n = 0 + 2 * (n/2) := Eq.symm $ heven ▸ Nat.mod_add_div n 2
  rw [Nat.zero_add, ←Nat.shiftLeft_one] at hn
  conv => lhs; rw [hn, ←Nat.lsb_shiftLeft]

@[simp]
protected
theorem lsb_getBit_zero (n : Nat) : n.lsb.getBit 0 = n.getBit 0 := by
  cases Nat.mod_two_eq_zero_or_one n
  case inl heven =>
    rw [
      Nat.lsb_of_even heven,
      Nat.shiftLeft_getBit,
      decide_eq_false (p:=0≥1) (by decide),
      Bool.false_and,
    ]
    conv => rhs; dsimp [getBit]; rw [heven]; reduce
  case inr hodd =>
    rw [Nat.lsb_of_odd hodd]; dsimp [getBit]; rw [hodd]; decide

protected
theorem lsb_getBit_iff (n : Nat) {i : Nat} : n.lsb.getBit i = true ↔ (n.getBit i = true ∧ (∀ j, j < i → n.getBit j = false)) := by
  induction n using recBase2 generalizing i
  case zero => simp
  case one =>
    conv => lhs; rw [Nat.lsb_of_odd (n:=1) (by decide)]
    constructor
    show getBit 1 i = true → getBit 1 i = true ∧ ∀ j, j < i → getBit 1 j = false
    . intro h; apply And.intro h
      have : i = 0 := by
        conv at h => lhs; change getBit (2^0) i; rw [Nat.getBit_two_pow]
        exact Eq.symm (of_decide_eq_true h)
      cases this
      intro _ hj; cases hj
    show getBit 1 i = true ∧ (∀ j, j < i → getBit 1 j = false) → getBit 1 i
    . exact And.left
  case div2 n h_ind =>
    cases i
    case zero =>
      rw [Nat.lsb_getBit_zero]
      constructor
      show (n+2).getBit 0 = true → (n+2).getBit zero = true ∧ ∀ j, j < 0 → _ 
      . intro h; apply And.intro h ?_
        intro _ hj; cases hj
      show (n+2).getBit zero = true ∧ _ → (n+2).getBit zero = true 
      . exact And.left
    case succ i =>
      cases Nat.mod_two_eq_zero_or_one n
      case inl heven =>
        have := calc
          n+2 = (n/2)*2 + 2 := by rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]
          _   = (n/2 + 1)*2 := Eq.symm $ Nat.add_mul ..
          _   = (n/2 + 1) <<< 1 := by rw [Nat.mul_comm, Nat.shiftLeft_one]
        simp only [
          this, ←Nat.lsb_shiftLeft,
          Nat.succ_eq_add_one,
          ←Nat.shiftRight_getBit,
          Nat.shiftLeft_shiftRight_self,
          Nat.shiftLeft_getBit
        ]
        suffices ∀ (m : Nat), (∀ j, j < i → m.getBit j = false) ↔ (∀ j, j < i.succ → (decide (j≥1) && m.getBit (j-1)) = false) by
          rw [←this]; exact h_ind
        intro m; constructor
        show (∀ j, j < i → m.getBit j = false) → (∀ j, j < i.succ → (decide (j≥ 1) && m.getBit (j-1)) = false)
        . intro h j hj
          cases j
          case zero =>
            rw [decide_eq_false (p:=zero ≥ 1) (by decide), Bool.false_and]
          case succ j =>
            have : j < i := lt_of_succ_lt_succ hj
            rw [decide_eq_true (p:=j.succ ≥ 1) j.zero_lt_succ, Bool.true_and, Nat.succ_sub_one]
            exact h j this
        show (∀ j, j < i.succ → (decide (j ≥ 1) && m.getBit (j-1)) = false) → _
        . intro h j hj
          have h_succ := h j.succ (Nat.succ_lt_succ hj)
          conv at h_succ =>
            rw [decide_eq_true (p:=j.succ≥1) j.zero_lt_succ, Bool.true_and, Nat.succ_sub_one]
          exact h_succ
      case inr hodd =>
        have := calc
          (n+2) % 2
            = n%2 := Nat.add_mod_right ..
          _ = 1 := hodd
        conv =>
          lhs; lhs
          rw [Nat.lsb_of_odd this]; dsimp [getBit]
          change getBit 0 i; rw [zero_getBit]
        suffices (n+2).getBit 0 = true by
          constructor
          . intro h; cases h
          . intro h; calc
              false = getBit (n+2) 0 := Eq.symm $ h.right 0 i.zero_lt_succ
              _     = true := this
        rw [Nat.getBit, decide_eq_true ‹(n+2)%2 = 1›]

#print axioms Nat.lsb_getBit_iff

protected
theorem eq_zero_of_lsb_eq_zero {n : Nat} : n.lsb = 0 → n = 0 := by
  intro h
  apply bitext
  intro i; rw [Nat.zero_getBit]
  induction i using Nat.recComplete
  case a.ind i h_ind =>
  cases hni : n.getBit i
  case false => rfl
  case true =>
    calc
      true = n.lsb.getBit i := Eq.symm $ n.lsb_getBit_iff.mpr ⟨hni, h_ind⟩
      _    = Nat.getBit 0 i := by rw [h]
      _    = false          := Nat.zero_getBit i


/-!
## Utility functions and lemmas
-/

/-- Bit-wise folding operation -/
def foldBitsL {α : Type u} (f : α → Bool → α) (init : α) (n : Nat) : α :=
  n.recBase2 (motive:=λ _ => α) init (f init true) (λ n a => f a (n % 2 == 1))

def countBits (n : Nat) : Nat := n.foldBitsL (λ n b => n + b.toUInt64.toNat) 0

def toDigitsBase2 (n : Nat) (pre : String := "0b"): String := n.foldBitsL (λ s b => s ++ if b then "1" else "0") pre

-- test
example : countBits 0b1001010111 = 6 := rfl
example : toDigitsBase2 0x55 "pre" = "pre1010101" := rfl

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
    rw [Nat.lor_zero, ←Nat.mul_two]
    rw [Nat.div_mul_cancel ((Nat.dvd_iff_mod_eq_zero 2 n).mpr hn)]
  by_cases n = 0
  case pos h => cases h; rw [if_pos rfl]
  case neg h => rw [if_neg h]

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

theorem log2'_zero : log2' 0 = 0 := rfl
theorem log2'_one : log2' 1 = 0 := rfl
theorem log2'_div2 (n : Nat) : log2' (n+2) = log2' (n/2+1) + 1 := by
  conv => lhs; unfold log2'; rw [recBase2_div2]

theorem log2'_mul2 (n : Nat) : log2' (2*n.succ) = (log2' n.succ) + 1 := by
  conv =>
    lhs; rw [Nat.mul_succ 2 n]; unfold log2'; rw [recBase2_div2]
    change log2' (2*n/2 + 1) + 1
    rw [Nat.mul_div_right n (Nat.zero_lt_succ 1)]

theorem log2'_mul2_of_pos {n : Nat} : n > 0 → log2' (2*n) = log2' n + 1 := by
  intro h
  have : n = (n-1) + 1 := Eq.symm $ Nat.sub_add_cancel h
  rw [this, log2'_mul2]

#print axioms Nat.log2'_mul2
#print axioms Nat.log2'_mul2_of_pos

theorem log2'_pow2 (k : Nat) : log2' (2^k) = k := by
  induction k
  case zero => exact log2'_one
  case succ k h_ind =>
    rw [
      Nat.pow_succ, Nat.mul_comm,
      log2'_mul2_of_pos (Nat.pos_pow_of_pos k (by decide)),
      h_ind
    ]

theorem zero_or_one_of_log2' : ∀ (n : Nat), n.log2' = 0 → n = 0 ∨ n = 1
| 0, _ => Or.inl rfl
| 1, _ => Or.inr rfl
| _+2, h => by cases log2'_div2 _ ▸ h

theorem ge_two_of_log2' : ∀ (n : Nat), n.log2' > 0 → n ≥ 2
| 0, h => by cases log2'_zero ▸ h
| 1, h => by cases log2'_one ▸ h
| _+2, _ => by rw [Nat.add_comm]; exact Nat.le.intro rfl

theorem log2'_le_self (n : Nat) : log2' n ≤ n := by
  induction n using recBase2
  case zero => decide
  case one => decide
  case div2 n h_ind =>
    suffices log2' (n/2 + 1) ≤ n+1
      from log2'_div2 n ▸ Nat.succ_le_succ this
    calc
      log2' (n/2 + 1)
        ≤ n/2 + 1 := h_ind
      _ ≤ n + 1 := Nat.succ_le_succ (Nat.div_le_self n 2)

theorem log2'_lt_self (n : Nat) : n > 0 → log2' n < n := by
  intro hpos
  induction n using recBase2
  case zero => cases hpos
  case one => decide
  case div2 n h_ind =>
    suffices log2' (n/2 + 1) < n+1
      from log2'_div2 n ▸ Nat.succ_lt_succ this
    calc
      log2' (n/2 + 1)
        < n/2 + 1 := h_ind (Nat.zero_lt_succ ..)
      _ ≤ n + 1 := Nat.succ_le_succ (Nat.div_le_self n 2)

theorem pow2_log2'_le_self {n : Nat} : n > 0 → 2 ^ n.log2' ≤ n := by
  intro h
  induction n using recBase2
  case zero => cases h
  case one => exact .refl
  case div2 n h_ind =>
    rw [log2'_div2]
    show 2^(log2' (n/2+1) + 1) ≤ n+2
    calc
      2^(log2' (n/2+1) + 1)
        = 2^(log2' (n/2+1)) * 2 := Nat.pow_succ 2 _
      _ ≤ (n/2+1) * 2 := Nat.mul_le_mul_right 2 (h_ind $ Nat.zero_lt_succ _)
      _ = n/2*2 + 2 := Nat.add_mul _ 1 2
      _ ≤ n+2 := Nat.add_le_add_right (Nat.div_mul_le_self n 2) 2

theorem log2'_le_log2' {m n : Nat} : m ≤ n → log2' m ≤ log2' n := by
  induction m using recBase2 generalizing n
  case zero => intros; exact Nat.zero_le _
  case one => intros; exact Nat.zero_le _
  case div2 m h_ind =>
    intro h
    let k := n-2
    have : n = k+2 := Eq.symm $ Nat.sub_add_cancel $ calc
      2 ≤ m+2 := Nat.le_add_left 2 m
      _ ≤ n := h
    rw [this]; unfold log2'; simp [recBase2_div2]
    conv => change (m/2+1).log2' + 1 ≤ (k/2+1).log2' + 1
    suffices m/2+1 ≤ k/2+1
      from Nat.succ_le_succ (h_ind this)
    suffices m ≤ k
      from Nat.succ_le_succ (div_le_div this)
    show m ≤ k;
      exact Nat.le_of_add_le_add_right (‹n=k+2› ▸ h)

theorem le_log2'_iff_pow2_le {k n : Nat} : n > 0 → (k ≤ n.log2' ↔ 2^k ≤ n) := by
  intros
  constructor
  show k ≤ n.log2' → 2^k ≤ n
  . intro h
    calc
      2^k ≤ 2^n.log2' := Nat.pow_le_pow_of_le_right (by decide) h
      _   ≤ n         := Nat.pow2_log2'_le_self ‹n>0›
  show 2^k ≤ n → k ≤ n.log2'
  . intro h
    calc
      k = log2' (2^k) := Eq.symm (log2'_pow2 k)
      _ ≤ log2' n     := log2'_le_log2' h


/--
A version of `Nat.log2` with rounding-up.
-/
@[inline]
def log2RU (n : Nat) : Nat := log2' ((n-1) <<< 1)

theorem log2RU_le_self : ∀ (n : Nat), log2RU n ≤ n
| 0 => by decide
| 1 => by decide
| n+2 => by
  dsimp [log2RU]; simp [Nat.mul_add, log2'_div2]
  suffices log2' (n+1) ≤ n+1
    from Nat.succ_le_succ this
  exact Nat.log2'_le_self _

theorem log2RU_lt_self : ∀ (n : Nat), n > 0 → log2RU n < n
| 1, _ => by decide
| n+2, _ => by
  dsimp [log2RU]; simp [Nat.mul_add, log2'_div2]
  suffices log2' (n+1) < n+1
    from Nat.succ_lt_succ this
  exact Nat.log2'_lt_self (n+1) n.zero_lt_succ

theorem lt_log2RU_iff_pow2_lt {k n : Nat} : k < log2RU n ↔ 2^k < n := by
  cases n
  case zero =>
    conv => lhs; rhs; reduce
    constructor <;> (intro h; cases h)
  case succ n =>
    dsimp [log2RU]; simp [log2RU]
    cases n
    case zero =>
      conv => lhs; rhs; reduce
      constructor
      . intro h; cases h
      . intro hlt1
        have : 2^k > 0 := Nat.pos_pow_of_pos k (by decide)
        exact absurd hlt1 (Nat.not_lt_of_le this)
    case succ n =>
      rw [log2'_mul2]
      have : ∀ (a b : Nat), (a < b+1) = (a ≤ b) :=
        λ a b => propext ⟨Nat.le_of_lt_succ, Nat.lt_succ_of_le⟩
      rw [this, this]
      exact le_log2'_iff_pow2_le n.zero_lt_succ

#print axioms lt_log2RU_iff_pow2_lt

theorem le_pow2_log2RU_self (n : Nat) : n ≤ 2^log2RU n := by
  cases Nat.lt_or_ge (2^log2RU n) n
  case inr hge => exact hge
  case inl hlt =>
    have : n.log2RU < n.log2RU := Nat.lt_log2RU_iff_pow2_lt.mpr hlt
    exact absurd this (Nat.lt_irrefl _)

end Nat