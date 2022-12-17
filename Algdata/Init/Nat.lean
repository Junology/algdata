/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

import Algdata.Init.Logic

namespace Nat

instance instNatLEDecidableRel : DecidableRel Nat.le := λ m n =>
  match m with
  | zero => Decidable.isTrue n.zero_le
  | succ m =>
    match n with
    | zero => Decidable.isFalse m.not_lt_zero
    | succ n =>
      match instNatLEDecidableRel m n with
      | isTrue h => Decidable.isTrue (Nat.succ_le_succ h)
      | isFalse h => Decidable.isFalse $ λ hcontra =>
        h (Nat.le_of_succ_le_succ hcontra)

instance instNatLTDecidableRel : DecidableRel Nat.lt := λ m n =>
  instNatLEDecidableRel m.succ n

theorem le_iff_eq_or_lt {m n : Nat} : m ≤ n ↔ (m = n ∨ m < n) where
  mp hle := by
    cases Nat.lt_or_ge m n
    case inl h => exact Or.inr h
    case inr h => exact Or.inl $ Nat.le_antisymm hle h
  mpr hor := by
    cases hor
    case inl heq => cases heq; simp
    case inr hlt => exact Nat.le_of_lt hlt

theorem ge_iff_eq_or_gt {m n : Nat} : m ≥ n ↔ (m = n ∨ m > n) :=
  Iff.trans le_iff_eq_or_lt $ Or.substIff (Iff.intro Eq.symm Eq.symm) (Iff.refl _)

theorem lt_iff_ne_and_ngt {m n : Nat} : m < n ↔ (m ≠ n ∧ ¬ m > n) where
  mp hlt := by
    constructor
    case left => exact ne_of_lt hlt
    case right =>
      rw [Nat.not_lt_eq]; exact Nat.le_of_lt hlt
  mpr hand := by
    cases Nat.lt_or_ge m n
    case inl hlt => exact hlt
    case inr hge =>
      apply False.elim
      cases le_iff_eq_or_lt.mp hge
      case inl heq =>
        exact hand.left heq.symm
      case inr hgt =>
        exact hand.right hgt

protected
theorem min_eq_right' {m n : Nat} (h : m ≥ n) : min m n = n := by
  rw [Nat.min_def]
  by_cases m ≤ n
  case pos hle =>
    have : m = n := Nat.le_antisymm hle h
    rw [if_pos hle, this]
  case neg hnle =>
    rw [if_neg hnle]

theorem min_succ_succ' (m n : Nat) : min m.succ n.succ = (min m n).succ := by
  by_cases m ≤ n
  case pos hle =>
    rw [Nat.min_eq_left hle, Nat.min_eq_left (Nat.succ_le_succ hle)]
  case neg hnle =>
    have : m ≥ n := Nat.le_of_lt (Nat.gt_of_not_le hnle)
    rw [Nat.min_eq_right' this, Nat.min_eq_right' (Nat.succ_le_succ this)]

theorem min_eq (n : Nat) : min n n = n := Nat.min_eq_left n.le_refl

theorem add_sub_assoc' {m k : Nat} : m ≤ k → ∀ (n : Nat), n + m - k = n - (k - m) := by
  intro hmk n
  have : k = (k-m) + m := Eq.symm $ Nat.sub_add_cancel hmk
  conv => lhs; rw [this, Nat.add_sub_add_right]

theorem lt_add_succ (n k : Nat) : n < n + k.succ := calc
  n ≤ n + k := Nat.le_add_right n k
  _ < (n+k).succ := Nat.lt_succ_self _
  _ = n + k.succ := Nat.add_succ n k

theorem lt_of_add_succ_eq {m k n : Nat} : m + k.succ = n → m < n := fun h =>
  calc
    m < m + k.succ := lt_add_succ m k
    _ = n := h

theorem not_lt_of_ge {m n : Nat} : m ≥ n → ¬(m < n) := by
  intro h hn
  exact Nat.not_le_of_gt hn h

theorem one_le_succ (n : Nat) : 1 ≤ n.succ :=
  n.casesOn (motive:=λ n => 1 ≤ n.succ) le.refl (λ n => Nat.succ_le_succ (zero_le n.succ))

theorem gt_zero_of_not_eq_zero {n : Nat} : n ≠ 0 → n > 0 :=
  n.casesOn (motive:=λ k => k≠0 → k > 0)
    (λ h => (h rfl).elim)
    (λ _ _ => Nat.zero_lt_succ _)

theorem ge_one_of_not_eq_zero {n : Nat} : n ≠ 0 → n ≥ 1 :=
  n.casesOn (motive:=λ n => n≠ 0 → n ≥ 1)
    (λ h => (h rfl).elim)
    (λ _ _ => one_le_succ _)

theorem add_pred {m n : Nat} : n > 0 → m + n.pred = (m+n).pred := by
  intro hn
  cases n
  case zero =>
    exact (zero.not_lt_zero hn).elim
  case succ n =>
    simp [Nat.add_succ]

theorem sub_lt_of_lt_add {l m n : Nat} : l ≥ n → l < m + n → l-n < m := by
  intro hln hlmn
  apply Nat.lt_of_add_lt_add_right
  rw [Nat.sub_add_cancel hln]
  assumption

theorem div_mod_unique (n : Nat) : ∀ {q₁ q₂ r₁ r₂ : Nat}, r₁ < n → r₂ < n → q₁*n + r₁ = q₂*n + r₂ → q₁=q₂ ∧ r₁=r₂ := by
  intros q₁ q₂ r₁ r₂ hr₁ hr₂ heq
  suffices q₁ = q₂ by
    constructor; assumption
    rw [this] at heq
    exact Nat.add_left_cancel heq
  revert q₂
  induction q₁
  case zero =>
    intro q₂ heq
    simp at *
    rw [heq] at hr₁
    cases q₂
    case zero => rfl
    case succ k =>
      rw [succ_mul, Nat.add_comm _ n, Nat.add_assoc] at hr₁
      conv at hr₁ =>
        rhs
        rw [←Nat.add_zero n]
      have : k*n+r₂ < 0 := Nat.lt_of_add_lt_add_left (k:=n) hr₁
      exact False.elim $ not_lt_zero _ this
  case succ q₁ h_ind =>
    intro q₂ heq
    rw [succ_mul, Nat.add_comm _ n, Nat.add_assoc] at heq
    cases q₂
    case zero =>
      simp at heq
      rw [←heq] at hr₂
      conv at hr₂ =>
        rhs
        rw [←Nat.add_zero n]
      have : q₁*n + r₁ < 0 :=
        Nat.lt_of_add_lt_add_left (k:=n) hr₂
      exact False.elim $ not_lt_zero _ this
    case succ q₂=>
      conv at heq =>
        rhs
        rw [succ_mul, Nat.add_comm _ n, Nat.add_assoc]
      apply congrArg succ
      apply h_ind
      exact Nat.add_left_cancel heq

/-
 - Ordering
-/
theorem compare_lt {m n : Nat} : m < n → compare m n = Ordering.lt := by
  intro h
  simp [compare, instOrdNat, compareOfLessAndEq]
  rw [if_pos h]

theorem compare_eq {m n : Nat} : m = n → compare m n = Ordering.eq := by
  intro h; cases h
  simp [compare, instOrdNat, compareOfLessAndEq]

theorem compare_gt {m n : Nat} : m > n → compare m n = Ordering.gt := by
  intro h
  simp [compare, instOrdNat, compareOfLessAndEq]
  have := lt_iff_ne_and_ngt.mp h
  rw [if_neg this.2, if_neg (this.1 ∘ Eq.symm)]

end Nat
