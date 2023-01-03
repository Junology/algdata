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

instance instToString [ToString α] : ToString (Matrix α r c) where
  toString a :=
    let optcomma : String → String
    | String.mk [] => ""
    | s => s ++ ","
    Fin.foldAll (n:=r) "" $ fun i s =>
      (optcomma s ++ "[" ++ · ++ "]") $
      Fin.foldAll (n:=c) "" $ fun j s =>
        optcomma s ++ toString (a.get i j)

instance instForM {m : Type _ → Type _} [Monad m] : ForM m (Matrix α r c) α where
  forM a f := a.entry.forM f

@[always_inline]
instance instGetElemMatrix {α : Type u} {r c : Nat} : GetElem (Matrix α r c) (Nat × Nat) α (λ _ i => i.1 < r ∧ i.2 < c) where
  getElem x i h := x.get ⟨i.1, h.left⟩ ⟨i.2, h.right⟩

end Matrix