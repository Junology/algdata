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
## The function `decide`
-/

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

/-
@[simp]
theorem Bool.not_and_self (a : Bool) : (!a && a) = false := by
  cases a <;> decide

@[simp]
theorem Bool.and_not_self (a : Bool) : (a && !a) = false := by
  cases a <;> decide
--/

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
