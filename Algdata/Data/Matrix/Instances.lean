/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Data.Matrix.Basic

universe u

namespace Matrix

variable {α β γ : Type _} {r k c : Nat}

instance instAdd [Add α] : Add (Matrix α r c) := Add.mk Matrix.add

instance instHAdd [HAdd α β γ] : HAdd (Matrix α r c) (Matrix β r c) (Matrix γ r c) := HAdd.mk Matrix.hAdd

instance instHMul [HMul α β γ] [HAdd γ γ γ] [OfNat γ (nat_lit 0)]: HMul (Matrix α r k) (Matrix β k c) (Matrix γ r c) where
  hMul := Matrix.hMul

instance instOfNat0 [OfNat α (nat_lit 0)] : OfNat (Matrix α r c) (nat_lit 0) where
  ofNat := Matrix.zero r c

instance instOfNat1 [OfNat α (nat_lit 0)] [OfNat α (nat_lit 1)] : OfNat (Matrix α r r) (nat_lit 1) where
  ofNat := Matrix.diagFn (n:=r) (λ _ => 1)

instance instRepr [Repr α] : Repr (Matrix α r c) where
  reprPrec x _ :=
    Lean.Format.bracket "{" (
      Lean.Format.joinSep [
        Lean.Format.group ("entry := " ++ repr x.entry),
        Lean.Format.group ("hsize := _")
      ] ", "
    ) "}"

instance instToString [ToString α] : ToString (Matrix α r c) where
  toString a := String.intercalate ", " $ List.ofFn (n:=r) λ i => toString a.entry[i*c:i*c+c]

instance instForM {m : Type _ → Type _} [Monad m] : ForM m (Matrix α r c) α where
  forM a f := a.entry.forM f

@[always_inline]
instance instGetElemMatrix {α : Type u} {r c : Nat} : GetElem (Matrix α r c) (Nat × Nat) α (λ _ i => i.1 < r ∧ i.2 < c) where
  getElem x i h := x.get ⟨i.1, h.left⟩ ⟨i.2, h.right⟩

end Matrix