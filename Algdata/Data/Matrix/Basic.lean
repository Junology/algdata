/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Basic
import Std.Data.Array.Lemmas
import Dijkstra.Control.Functor.Subreg

import Algdata.Init.Nat
import Algdata.Init.Fin
import Algdata.Init.GetElem
import Algdata.Data.Array.Lemmas
import Algdata.Data.Array.Modify

universe u v w

@[unbox]
structure Matrix (α : Type u) (r c : Nat) where
  entry : Array α
  hsize : entry.size = r * c

attribute [simp] Matrix.hsize

namespace Matrix



/-!
## Basic operations
-/

section BasicOp

variable {α : Type u} {r c : Nat}

--- Get the `(i,j)`-entry of a given matrix
def get (a : @& Matrix α r c) (i : @& Fin r) (j : @& Fin c) : α :=
  a.entry[a.hsize.symm ▸ Fin.lexFold i j]

--- Substitute a value into the `(i,j)`-entry of a given matrix
def set (a : Matrix α r c) (i : @& Fin r) (j : @& Fin c) (v : α) : Matrix α r c where
  entry := a.entry.set (a.hsize.symm ▸ Fin.lexFold i j) v
  hsize := (Array.size_set a.entry _ v).symm ▸ a.hsize

--- Counterpart of `Array.get_set_eq`
@[simp]
theorem get_set_eq (a : Matrix α r c) (i : Fin r) (j : Fin c) (v : α) : get (a.set i j v) i j = v := by
  dsimp [get, set]
  rw [getElem_eq (by rw [Fin.subst_eq]) (Fin.subst_val _)]
  dsimp [Fin.lexFold]
  rw [Array.get_set_eq a.entry]

--- Counterpart of `Array.get_set_ne` for distinct rwo indices.
theorem get_set_ne_row (a : Matrix α r c) {i₁ i₂ : Fin r} (h : i₁ ≠ i₂) (j : Fin c) (v : α) : get (a.set i₁ j v) i₂ j = get a i₂ j := by
  dsimp [set, get]
  conv => lhs; rw [getElem_eq (by rw [Fin.subst_eq]) (Fin.subst_val _)]
  conv => rhs; rw [getElem_eq rfl (Fin.subst_val _)]
  apply Array.get_set_ne a.entry
  dsimp
  intro hcontra
  have := Fin.lexFold_inj (Fin.eq_of_val_eq hcontra)
  exact absurd this.left h

--- Counterpart of `Array.get_set_ne` for distinct column indices.
theorem get_set_ne_col (a : Matrix α r c) (i : Fin r) {j₁ j₂ : Fin c} (h : j₁ ≠ j₂) (v : α) : get (a.set i j₁ v) i j₂ = get a i j₂ := by
  dsimp [set, get]
  conv => lhs; rw [getElem_eq (by rw [Fin.subst_eq]) (Fin.subst_val _)]
  conv => rhs; rw [getElem_eq rfl (Fin.subst_val _)]
  apply Array.get_set_ne a.entry
  dsimp
  intro hcontra
  have := Fin.lexFold_inj (Fin.eq_of_val_eq hcontra)
  exact absurd this.right h

end BasicOp


/-!
## Construction of matrices
-/

section Construction

variable {α : Type u}

--- Define a matrix whose entries are specified by a function
def ofFn {r c : Nat} (f : Fin r → Fin c → α) : Matrix α r c where
  entry := Array.ofFn (n:=r*c) $ λ k =>
    have : c > 0 := by
      cases Nat.eq_zero_or_pos c
      case inl h =>
        cases h
        cases k with | mk k hk =>
        rw [Nat.mul_zero] at hk
        exact absurd hk (Nat.not_lt_zero k)
      case inr h => exact h
    let i : Fin r := Fin.mk (k / c) ((Nat.div_lt_iff_lt_mul this).mpr k.isLt)
    let j : Fin c := Fin.mk (k % c) (Nat.mod_lt _ this)
    f i j
  hsize := Array.size_ofFn _

--- Constructing the zero matrix with given size
def zero [OfNat α (nat_lit 0)] (r c : Nat) : Matrix α r c where
  entry := Array.mkArray (r*c) 0
  hsize := Array.size_mkArray _ _

--- A square diagonal matrix with given array as diagonal
def diag {α : Type u} [OfNat α (nat_lit 0)] (ds : Array α) : Matrix α ds.size ds.size :=
  Fin.foldAll (n:=ds.size) (λ i x => x.set i i ds[i]) (zero ds.size ds.size)

--- A square diagonal matrix whose diagonal entries are specified by a function
def diagFn {α : Type u} [OfNat α (nat_lit 0)] {n : Nat} (f : Fin n → α) : Matrix α n n :=
  Fin.foldAll (n:=n) (λ i x => x.set i i (f i)) (zero n n)

end Construction


/-!
## modifyM

Apply a (monadic) operation to specific entries of a matrix.

-/

section modifyM

variable {α : Type u} {r c : Nat}

-- cf. modifyMUnsafe in Init.Data.Array.Basic
def modifyM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → m α) : m (Matrix α r c) := do
  let v ← f (a.get i j)
  pure $ a.set i j v

-- use `Array.modifyM` function directly
-- TODO: performance comparison with `modifyM` above
def modifyM' {m : Type _ → Type _} [Monad m] [LawfulMonad m] [SubregFunctor m] (a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → m α) : m (Matrix α r c) := do
  let w ← SubregFunctor.ensureF _ (a.entry.size_modifyM (i.val*c + j.val) f)
  pure {entry:=w.val, hsize:=by rw[w.property,a.hsize]}

def modify (a : Matrix α r c) (i : Fin r) (j : Fin c) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyM i j f

def modifyRowM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (f : α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=c) (λ j b => b.modifyM i j f) a

def modifyRow (a : Matrix α r c) (i : Fin r) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyRowM i f

def modifyColM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (j : Fin c) (f : α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=r) (λ i b => b.modifyM i j f) a

def modifyCol (a : Matrix α r c) (j : Fin c) (f : α → α) : Matrix α r c :=
  Id.run <| a.modifyColM j f

-- Modification of a row with column indices
def modifyRowIdxM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (i : Fin r) (f : Fin c → α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=c) (λ j b => b.modifyM i j (f j)) a

def modifyRowIdx (a : Matrix α r c) (i : Fin r) (f : Fin c → α → α) : Matrix α r c :=
  Id.run <| a.modifyRowIdxM i f

-- Modificaion of a column with row indices
def modifyColIdxM {m : Type _ → Type _} [Monad m] (a : Matrix α r c) (j : Fin c) (f : Fin r → α → m α) : m (Matrix α r c) :=
  Fin.foldAllM (n:=r) (λ i b => b.modifyM i j (f i)) a

def modifyColIdx (a : Matrix α r c) (j : Fin c) (f : Fin r → α → α) : Matrix α r c :=
  Id.run <| a.modifyColIdxM j f

end modifyM


/-!
## Arithmetic operations
-/

section Addition

variable {α β γ : Type _} {r c : Nat}

def zipWith {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (x : Matrix α r c) (y : Matrix β r c) : Matrix γ r c where
  entry := Array.zipWith x.entry y.entry f
  hsize := by rw [Array.zipWith_size, x.hsize, y.hsize, Nat.min_eq]

def add [Add α] : Matrix α r c → Matrix α r c → Matrix α r c := zipWith (·+·)

def hAdd [HAdd α β γ] : Matrix α r c → Matrix β r c → Matrix γ r c := zipWith (·+·)

end Addition

section Multiplication

variable {α β γ : Type _} [ToString α] [ToString β] [ToString γ]{r k c : Nat}

def hMul [HMul α β γ] [HAdd γ γ γ] [OfNat γ (nat_lit 0)] (x : Matrix α r k) (y : Matrix β k c) : Matrix γ r c :=
  ofFn (λ i j => Fin.foldAll (n:=k) (λ s a => a + x.get i s * y.get s j) 0)

end Multiplication

/-!
## BLAS-like interfaces
-/

section BLAS

variable {α : Type u} {β : Type v} {γ : Type w} {r c : Nat}

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
  Fin.foldAll (n:=c)
    (fun j a => {
      entry := a.entry.swap (a.hsize.symm ▸ Fin.lexFold i₁ j) (a.hsize.symm ▸ Fin.lexFold i₂ j)
      hsize := by rw [Array.size_swap, a.hsize]
    })
    a

-- Swap two columns
def swapCol (a : Matrix α r c) (j₁ j₂ : Fin c) : Matrix α r c :=
  Fin.foldAll (n:=r)
    (fun i a => {
      entry := a.entry.swap (a.hsize.symm ▸ Fin.lexFold i j₁) (a.hsize.symm ▸ Fin.lexFold i j₂)
      hsize := by rw [Array.size_swap, a.hsize]
    })
    a

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

end BLAS

end Matrix

