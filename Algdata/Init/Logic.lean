/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic

import Algdata.Tactic.PkgLocal

universe u

/-!
# Basic lemmas on the logical operators
-/

/-!
## The function `decide`
-/

section Decide

variable {α : Sort u} [DecidableEq α]

@[pkg_local]
private theorem and_decideEq (f : α → Bool) (a b : α) : (f a && decide (a=b)) = (f b && decide (a=b)) := by
  apply Decidable.byCases (p:=a=b) <;> (intro h; simp [h])

@[pkg_local]
private theorem decideEq_and (f : α → Bool) (a b : α) : (decide (a=b) && f a) = (decide (a=b) && f b) := by
  apply Decidable.byCases (p:=a=b) <;> (intro h; simp [h])

@[pkg_local]
private theorem decide_and_decide {p q : Prop} [Decidable p] [Decidable q] : (decide p && decide q) = decide (p ∧ q) := by
  apply Decidable.byCases (p:=p) <;> apply Decidable.byCases (p:=q)
  <;> (intro hq hp; simp [hp,hq])

end Decide


/-!
## Bool operators
-/

namespace Bool

@[pkg_local]
private theorem and_comm (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> decide

@[pkg_local]
private theorem bne_and (a b c : Bool) : ((a != b) && c) = ((a && c) != (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

@[pkg_local]
private theorem and_bne (a b c : Bool) : (a && (b != c)) = ((a && b) != (a && c)) := by
  cases a <;> cases b <;> cases c <;> decide

@[pkg_local]
private theorem bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> decide

@[pkg_local, simp]
private theorem bne_false (a : Bool) : (a != false) = a := by
  cases a <;> decide

@[pkg_local, simp]
private theorem false_bne (a : Bool) : (false != a) = a := by
  cases a <;> decide

@[pkg_local, simp]
private theorem bne_true (a : Bool) : (a != true) = !a := by
  cases a <;> decide

@[pkg_local, simp]
private theorem true_bne (a : Bool) : (true != a) = !a := by
  cases a <;> decide

end Bool
