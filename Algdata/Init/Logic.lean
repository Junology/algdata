/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic

universe u

/-!
# Basic lemmas on the logical operators
-/

/-!
## Logical connectives
-/

theorem And.map {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ → p₂) (hq : q₁ → q₂) : p₁ ∧ q₁ → p₂ ∧ q₂
| And.intro hp₁ hq₁ => And.intro (hp hp₁) (hq hq₁)

theorem And.substIff {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ ↔ p₂) (hq : q₁ ↔ q₂) : (p₁ ∧ q₁) ↔ (p₂ ∧ q₂) where
  mp h1 := h1.map hp.mp hq.mp
  mpr h2 := h2.map hp.mpr hq.mpr

theorem Or.map {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ → p₂) (hq : q₁ → q₂) : p₁ ∨ q₁ → p₂ ∨ q₂
| Or.inl hp₁ => Or.inl (hp hp₁)
| Or.inr hq₁ => Or.inr (hq hq₁)

theorem Or.substIff {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ ↔ p₂) (hq : q₁ ↔ q₂) : (p₁ ∨ q₁ ↔  p₂ ∨ q₂) where
  mp h1 := h1.map hp.mp hq.mp
  mpr h2 := h2.map hp.mpr hq.mpr

/-- Functoriality of `if-then-else`. -/
theorem app_ite {p : Prop} [Decidable p] (f : α → β) (a_true a_false : α) : f (ite p a_true a_false) = ite p (f a_true) (f a_false) := by
  by_cases h : p <;> simp [h]


/-!
## The function `decide`
-/

theorem decide_eq_decide_of_iff {p q : Prop} [Decidable p] [Decidable q] : (p ↔ q) → decide p = decide q := by
  intro h
  apply Decidable.byCases (p:=p) <;> apply Decidable.byCases (p:=q)
  <;> (intro hq hp; simp [hp,hq])
  . exact hq (h.mp hp)
  . exact hp (h.mpr hq)

theorem and_decideEq {α : Sort u} [DecidableEq α] (f : α → Bool) (a b : α) : (f a && decide (a=b)) = (f b && decide (a=b)) := by
  apply Decidable.byCases (p:=a=b) <;> (intro h; simp [h])

theorem decideEq_and {α : Sort u} [DecidableEq α] (f : α → Bool) (a b : α) : (decide (a=b) && f a) = (decide (a=b) && f b) := by
  apply Decidable.byCases (p:=a=b) <;> (intro h; simp [h])

theorem decide_and_decide {p q : Prop} [Decidable p] [Decidable q] : (decide p && decide q) = decide (p ∧ q) := by
  apply Decidable.byCases (p:=p) <;> apply Decidable.byCases (p:=q)
  <;> (intro hq hp; simp [hp,hq])


/-!
## Bool operators
-/

theorem Bool.and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> decide

@[simp]
theorem Bool.not_and_self (a : Bool) : (!a && a) = false := by
  cases a <;> decide

@[simp]
theorem Bool.and_not_self (a : Bool) : (a && !a) = false := by
  cases a <;> decide

theorem Bool.bne_and (a b c : Bool) : ((a != b) && c) = ((a && c) != (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem Bool.and_bne (a b c : Bool) : (a && (b != c)) = ((a && b) != (a && c)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem Bool.bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> decide

@[simp]
theorem Bool.bne_false (a : Bool) : (a != false) = a := by
  cases a <;> decide

@[simp]
theorem Bool.false_bne (a : Bool) : (false != a) = a := by
  cases a <;> decide

@[simp]
theorem Bool.bne_true (a : Bool) : (a != true) = !a := by
  cases a <;> decide

@[simp]
theorem Bool.true_bne (a : Bool) : (true != a) = !a := by
  cases a <;> decide
