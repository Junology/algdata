/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Fin.Lemmas

import Algdata.Init.Nat

universe u v w

namespace Fin

theorem val_succ_eq_succ_val {n : Nat} (x : Fin n) : x.succ.val = x.val.succ := rfl

def pred {n : Nat} (x : Fin n) (h : x.val > 0) : Fin n.pred where
  val := x.val.pred
  isLt := Nat.pred_lt_pred (Nat.not_eq_zero_of_lt h) x.isLt

@[simp]
theorem subst_eq : ∀ {n k : Nat} {h : n = k} (x : Fin n), h ▸ x = ⟨x.val, h ▸ x.isLt⟩
| _, _, rfl, mk _ _ => rfl

@[simp]
theorem subst_val : ∀ {n k : Nat} {h : n = k} (x : Fin n), (h ▸ x).val = x.val
| _, _, rfl, mk _ _ => rfl

theorem lexfold_lt_mul {m n : Nat} (x : Fin m) (y : Fin n) : x.val * n + y.val < m*n :=
  calc
    x.val * n + y.val
      < x.val * n + n := Nat.add_lt_add_left y.isLt _
    _ = (x.val.succ)*n := (Nat.succ_mul x.val n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt x.isLt)

theorem lexfold_inj {m n : Nat} {x₁ x₂: Fin m} {y₁ y₂ : Fin n} (h : x₁.val * n + y₁.val = x₂.val * n + y₂.val) : x₁=x₂ ∧ y₁=y₂ := by
  have : x₁.val = x₂.val ∧ y₁.val = y₂.val := Nat.div_mod_unique n y₁.isLt y₂.isLt h
  exact ⟨Fin.eq_of_val_eq this.left, Fin.eq_of_val_eq this.right⟩

-- Folding a product of two finite sets into a finite set in the lexicographical order
@[always_inline]
def lexFold {m n : Nat} (x : Fin m) (y : Fin n) : Fin (m*n) where
  val := x.val * n + y.val
  isLt := lexfold_lt_mul x y

def lexFold_inj {m n : Nat} {x₁ x₂ : Fin m} {y₁ y₂ : Fin n} (h : lexFold x₁ y₁ = lexFold x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ :=
  lexfold_inj (congrArg val h)

@[inline]
def foldAllM {m : Type u → Type v} [Monad m] {n : Nat} {α : Type u} (init : α) (f : Fin n → α → m α) : m α :=
  let rec @[specialize] loop (i : Nat) (x : α) : (k : Nat) → (i+k = n) → m α
  | 0, _ => pure x
  | k+1, h => do
    loop i.succ (← f ⟨i,Nat.lt_of_add_succ_eq h⟩ x) k (by rw [←h, Nat.add_succ, Nat.succ_add])
  loop 0 init n (Nat.zero_add n)

@[inline]
def foldAll {n : Nat} {α : Type u} (init : α) (f : Fin n → α → α) : α :=
  Id.run <| foldAllM init f

@[inline]
def forAllM {m : Type u → Type v} [Monad m] {n : Nat} (f : Fin n → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Nat) : (k : Nat) → (i+k = n) → m PUnit
  | 0, _ => pure PUnit.unit
  | k+1, h => do
    f ⟨i,Nat.lt_of_add_succ_eq h⟩
    loop i.succ k (by rw [←h, Nat.add_succ, Nat.succ_add])
  loop 0 n (Nat.zero_add n)

protected
def elementList : (n : Nat) → List (Fin n)
| 0 => []
| (n+1) => ⟨0, n.zero_lt_succ⟩ :: List.map (λ (⟨i,h⟩ : Fin n) => ⟨i+1, i.succ_lt_succ h⟩) (Fin.elementList n)

protected
theorem length_elementList (n : Nat) : List.length (Fin.elementList n) = n := by
  induction n
  case zero => rfl
  case succ n h_ind => unfold Fin.elementList; unfold List.length; rw [List.length_map, h_ind]

end Fin
