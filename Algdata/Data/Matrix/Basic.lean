/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Control.Prop
import Algdata.Control.MonadProp
import Algdata.Init.Nat
import Algdata.Init.Fin
import Algdata.Data.Array.Basic
import Algdata.Data.Array.Modify

structure Matrix (α : Type _) (r c : Nat) where
  entry : Array α
  hsize : entry.size = r * c

namespace Matrix

variable {α β γ : Type _} {r c : Nat}

def zipWith (f : α → β → γ) (x : Matrix α r c) (y : Matrix β r c) : Matrix γ r c where
  entry := Array.zipWith x.entry y.entry f
  hsize := by rw [Array.zipWith_size, x.hsize, y.hsize, Nat.min_eq]

def add [Add α] : Matrix α r c → Matrix α r c → Matrix α r c := zipWith (·+·)

def hAdd [HAdd α β γ] : Matrix α r c → Matrix β r c → Matrix γ r c := zipWith (·+·)

def get (a : Matrix α r c) (i : Fin r) (j : Fin c) : α :=
  a.entry.get (a.hsize.symm ▸ Fin.lexFold i j)

def set (a : Matrix α r c) (i : Fin r) (j : Fin c) (v : α) : Matrix α r c where
  entry := a.entry.set (a.hsize.symm ▸ Fin.lexFold i j) v
  hsize := by simp; exact a.hsize

@[simp]
theorem get_set_on (a : Matrix α r c) (i : Fin r) (j : Fin c) (v : α) : get (a.set i j v) i j = v := by
  unfold get
  unfold Fin.lexFold
  unfold set
  rw [Array.get_set_on a.entry (a.hsize.symm ▸ Fin.lexFold i j)]
  rw [Fin.val_of_subst, Fin.val_of_subst]
  rfl

theorem get_set_off_row (a : Matrix α r c) {i₁ i₂ : Fin r} (h : i₁ ≠ i₂) (j : Fin c) (v : α) : get (a.set i₁ j v) i₂ j = get a i₂ j := by
  unfold get; unfold Fin.lexFold
  unfold set
  rw [Array.get_set_off a.entry]
  apply congrArg (Array.get a.entry)
  apply Fin.eq_of_val_eq
  rw [Fin.val_of_subst, Fin.val_of_subst]
  rw [Fin.val_of_subst, Fin.val_of_subst]
  unfold Fin.lexFold
  simp
  intro hcontra
  have : i₁.val = i₂.val := (Nat.div_mod_unique c j.isLt j.isLt hcontra).left
  exact (h (Fin.eq_of_val_eq this))

theorem get_set_off_col (a : Matrix α r c) (i : Fin r) {j₁ j₂ : Fin c} (h : j₁ ≠ j₂) (v : α) : get (a.set i j₁ v) i j₂ = get a i j₂ := by
  unfold get; unfold Fin.lexFold
  unfold set
  rw [Array.get_set_off a.entry]
  apply congrArg (Array.get a.entry)
  apply Fin.eq_of_val_eq
  rw [Fin.val_of_subst, Fin.val_of_subst]
  rw [Fin.val_of_subst, Fin.val_of_subst]
  unfold Fin.lexFold
  simp
  intro hcontra
  have : j₁.val = j₂.val := (Nat.div_mod_unique c j₁.isLt j₂.isLt hcontra).right
  exact (h (Fin.eq_of_val_eq this))

-- cf. modifyMUnsafe in Init.Data.Array.Basic
def modifyM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → m α) : m (Matrix α r c) := do
  let v ← f (a.get i j)
  pure $ a.set i j v

-- use `Array.modifyM` function directly
-- TODO: performance comparison with `modifyM` above
def modifyM' {m : Type _ → Type _} [Monad m] [LawfulMonad m] [MonadProp m](a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → m α) : m (Matrix α r c) := do
  let w ← MonadProp.ensure _ (a.entry.size_modifyM (i.val*c + j.val) f)
  pure {entry:=w.val, hsize:=by rw[w.property,a.hsize]}

def modify (a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyM i j f

def modifyRowM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (f : α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=c) a $
    fun j b => b.modifyM i j f

def modifyRow (a : Matrix α r c) (i : Fin r) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyRowM i f

def modifyColM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (j : Fin c) (f : α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=r) a $
    fun i b => b.modifyM i j f

def modifyCol (a : Matrix α r c) (j : Fin c) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyColM j f

-- Modification of a row with column indices
def modifyRowIdxM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (f : Fin c → α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=c) a $
    fun j b => b.modifyM i j (f j)

def modifyRowIdx (a : Matrix α r c) (i : Fin r) (f : Fin c → α → α) : Matrix α r c :=
  Id.run <| a.modifyRowIdxM i f

-- Modificaion of a column with row indices
def modifyColIdxM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (j : Fin c) (f : Fin r → α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=r) a $
    fun i b => b.modifyM i j (f i)

def modifyColIdx (a : Matrix α r c) (j : Fin c) (f : Fin r → α → α) : Matrix α r c :=
  Id.run <| a.modifyColIdxM j f

-- Scalar multiplication on a row from left
def scalarLeftRow [HMul α β β] (a : Matrix β r c) (coeff : α) (i : Fin r) : Matrix β r c :=
  a.modifyRow i (coeff * ·)

-- Scalar multiplication on a row from right
def scalarRightRow [HMul α β α] (a : Matrix α r c) (i : Fin r) (coeff : β) : Matrix α r c :=
  a.modifyRow i (· * coeff)

-- Scalar multiplication on a column from left
def scalarLeftCol [HMul α β β] (a : Matrix β r c) (coeff : α) (j : Fin c) : Matrix β r c :=
  a.modifyCol j (coeff * ·)

-- Scalar multiplication on a column from right
def scalarRightCol [HMul α β α] (a : Matrix α r c) (j : Fin c) (coeff : β) : Matrix α r c :=
  a.modifyCol j (· * coeff)

-- Swap two rows
def swapRow (a : Matrix α r c) (i₁ i₂ : Fin r) : Matrix α r c :=
  Fin.foldAll (n:=c) a $
    fun j a => {
      entry := a.entry.swap (a.hsize.symm ▸ Fin.lexFold i₁ j) (a.hsize.symm ▸ Fin.lexFold i₂ j)
      hsize := by rw [Array.size_swap, a.hsize]
    }

-- Swap two columns
def swapCol (a : Matrix α r c) (j₁ j₂ : Fin c) : Matrix α r c :=
  Fin.foldAll (n:=r) a $
    fun i a => {
      entry := a.entry.swap (a.hsize.symm ▸ Fin.lexFold i j₁) (a.hsize.symm ▸ Fin.lexFold i j₂)
      hsize := by rw [Array.size_swap, a.hsize]
    }

-- Add a scalar multiple of a row to another
-- The multiplication is performed from left: `y ← a*x + y`
def axpyRow [HMul α β γ] [HAdd γ β β] (a : Matrix β r c) (coeff : α) (isrc : Fin r) (itgt : Fin r) : Matrix β r c:=
  a.modifyRowIdx itgt $
    fun j x => coeff * a.get isrc j + x

-- Add a scalar multiple of a row to another
-- The multiplication is performed from right: `y ← x*a + y`
def xapyRow [HMul α β γ] [HAdd γ α α] (a : Matrix α r c) (isrc : Fin r) (coeff : β) (itgt : Fin r) : Matrix α r c :=
  a.modifyRowIdx itgt $
    fun j x => a.get isrc j * coeff + x

-- Add a scalar multiple of a column to another
-- The multiplication is performed from left: `y ← a*x + y`
def axpyCol [HMul α β γ] [HAdd γ β β] (a : Matrix β r c) (coeff : α) (jsrc : Fin c) (jtgt : Fin c) : Matrix β r c :=
  a.modifyColIdx jtgt $
    fun i x => coeff * a.get i jsrc + x

-- Add a scalar multiple of a column to another
-- The multiplication is performed from right: `y ← x*a + y`
def xapyCol [HMul α β γ] [HAdd γ α α] (a : Matrix α r c) (jsrc : Fin c) (coeff : β) (jtgt : Fin c) : Matrix α r c :=
  a.modifyColIdx jtgt $
    fun i x => a.get i jsrc * coeff + x

end Matrix

