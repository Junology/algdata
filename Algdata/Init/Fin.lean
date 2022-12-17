/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Fin.Lemmas

import Algdata.Init.Nat

namespace Fin

theorem val_succ_eq_succ_val {n : Nat} (x : Fin n) : x.succ.val = x.val.succ := rfl

def pred {n : Nat} (x : Fin n) (h : x.val > 0) : Fin n.pred where
  val := x.val.pred
  isLt := Nat.pred_lt_pred (Nat.not_eq_zero_of_lt h) x.isLt

theorem val_of_subst {n k : Nat} (h : n = k) (x : Fin n) : (Eq.ndrec (motive := Fin) x h).val = x.val := by cases h; rfl

theorem subst_match {n k : Nat} (h : n = k) (x : Fin n) : (Eq.ndrec (motive := Fin) x h) = ⟨x.val, h ▸ x.isLt⟩ :=
  eq_of_val_eq (x.val_of_subst h)

theorem subst_mk {n k : Nat} (h : n = k) (i : Nat) (hLt : i < n) : (Eq.ndrec (motive := Fin) (Fin.mk i hLt) h) = Fin.mk i (h ▸ hLt) := by cases h; rfl

-- Folding a product of two finite sets into a finite set in the lexicographical order
def lexFold {m n : Nat} (x : Fin m) (y : Fin n) : Fin (m*n) where
  val := x.val * n + y.val
  isLt := calc
    x.val * n + y.val
      < x.val * n + n := Nat.add_lt_add_left y.isLt _
    _ = (x.val.succ)*n := (Nat.succ_mul x.val n).symm
    _ ≤ m*n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt x.isLt)

def lexFold_inj {m n : Nat} {x₁ x₂ : Fin m} {y₁ y₂ : Fin n} : lexFold x₁ y₁ = lexFold x₂ y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
  intro h
  unfold lexFold at h
  have : x₁.val = x₂.val ∧ y₁.val = y₂.val := Nat.div_mod_unique n y₁.isLt y₂.isLt (congrArg val h)
  constructor <;> apply Fin.eq_of_val_eq
  case left => exact this.left
  case right => exact this.right

def foldAllM {m : Type _ → Type _} [Monad m] {n : Nat} {α : Type _} (init : α) (f : Fin n → α → m α) : m α :=
  let rec loop (i : Nat) (x : α) : (k : Nat) → (i+k = n) → m α
  | 0, _ => pure x
  | k+1, h => do
    loop i.succ (← f ⟨i,Nat.lt_of_add_succ_eq h⟩ x) k (by rw [←h, Nat.add_succ, Nat.succ_add])
  loop 0 init n (Nat.zero_add n)

def foldAll {n : Nat} {α : Type _} (init : α) (f : Fin n → α → α) : α :=
  Id.run <| foldAllM init f

def forAllM {m : Type _ → Type _} [Monad m] {n : Nat} (f : Fin n → m PUnit) : m PUnit :=
  let rec loop (i : Nat) : (k : Nat) → (i+k = n) → m PUnit
  | 0, _ => pure ()
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
