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

/--
Analogue of `Nat.foldM`; this traverses all elements of `Fin n` in the ascending order.
@todo Compare it with the following implementation regarding the perfomance:
```
@[inline]
def foldAllM' {α : Type u} (f : Fin n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : (k : Nat) → k ≤ n → α → m α
  | 0, _, x => pure x
  | k+1, h, x => f ⟨n-k-1, Nat.sub_lt_self k.zero_lt_succ h⟩ x >>= loop k (Nat.le_of_succ_le h)
  loop n n.le.refl init
```
-/
@[inline]
def foldAllM {m : Type u → Type v} [Monad m] {n : Nat} {α : Type u} (f : Fin n → α → m α) (init : α) : m α :=
  let rec @[specialize] loop (i : Nat) (x : α) : (k : Nat) → (i+k = n) → m α
  | 0, _ => pure x
  | k+1, h => do
    loop i.succ (← f ⟨i,Nat.lt_of_add_succ_eq h⟩ x) k (by rw [←h, Nat.add_succ, Nat.succ_add])
  loop 0 init n (Nat.zero_add n)

@[inline]
def foldAll {n : Nat} {α : Type u} (f : Fin n → α → α) (init : α) : α :=
  Id.run <| foldAllM f init

@[inline]
def forAllM {m : Type u → Type v} [Monad m] {n : Nat} (f : Fin n → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Nat) : (k : Nat) → (i+k = n) → m PUnit
  | 0, _ => pure PUnit.unit
  | k+1, h => do
    f ⟨i,Nat.lt_of_add_succ_eq h⟩
    loop i.succ k (by rw [←h, Nat.add_succ, Nat.succ_add])
  loop 0 n (Nat.zero_add n)

theorem foldAllM.loop_succ {m : Type u → Type v} [Monad m] {α : Type u} {n : Nat} {f : Fin (n+1) → α → m α} {i : Nat} {a : α} {k : Nat} {h : i+(k+1)=n+1} : Fin.foldAllM.loop f i a (k+1) h = f ⟨i, Nat.lt_of_add_succ_eq h⟩ a >>= λ b => Fin.foldAllM.loop (f ∘ Fin.succ) i b k (Nat.succ.inj h) := by
  induction k generalizing n f i a
  case zero => rfl
  case succ k h_ind =>
    conv =>
      lhs
      change do loop f i.succ (← f ⟨i,Nat.lt_of_add_succ_eq h⟩ a) k.succ (by rw [←h]; rw [Nat.add_succ, Nat.succ_add, Nat.add_succ]; rfl)
    apply bind_congr; intro b
    rw [h_ind]
    rfl

theorem foldAllM_zero {m : Type u → Type v} [Monad m] {α : Type u} {init : α} {f : Fin 0 → α → m α} : Fin.foldAllM f init = pure (f:=m) init := rfl
theorem foldAllM_succ {m : Type u → Type v} [Monad m] {α : Type u} {init : α} {f : Fin n.succ → α → m α} : Fin.foldAllM f init = f ⟨0, Nat.zero_lt_succ n⟩ init >>= Fin.foldAllM (f ∘ Fin.succ) := by
  dsimp [foldAllM]; rw [Fin.foldAllM.loop_succ]

@[simp]
theorem foldAll_zero {α : Type u} {f : Fin 0 → α → α} {init : α} : Fin.foldAll f init = init := rfl

@[simp]
theorem foldAll_succ {α : Type u} {n : Nat} {f : Fin n.succ → α → α} {init : α} : Fin.foldAll f init = Fin.foldAll (f ∘ Fin.succ) (f ⟨0, Nat.zero_lt_succ n⟩ init) := by
  unfold Fin.foldAll; rw [foldAllM_succ]; rfl

theorem foldAllM_comp_val {m : Type u → Type v} [Monad m] {n : Nat} {α : Type u} {f : Nat → α → m α} {init : α} : foldAllM (n:=n) (f ∘ Fin.val) init = Nat.foldM f init n := by
  induction n generalizing f init
  case zero => rfl
  case succ n h_ind =>
    rw [foldAllM_succ]; dsimp
    have : (f ∘ Fin.val (n:=n+1)) ∘ Fin.succ = (f ∘ Nat.succ) ∘ Fin.val := by
      apply funext; intro x; dsimp; rw [Fin.val_succ_eq_succ_val]
    conv => lhs; rhs; rw [this]; ext x; rw [h_ind]
    conv => rhs; rw [Nat.foldM_succ]

theorem foldAll_comp_val {n : Nat} {α : Type u} {f : Nat → α → α} {init : α} : foldAll (n:=n) (f ∘ Fin.val) init = Nat.fold f n init := by
  unfold foldAll; rw [Nat.fold_eq_foldM, foldAllM_comp_val]; rfl

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
