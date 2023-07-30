/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.LawfulLT

namespace Sigma

universe u v

-- Relation on the first component
def relOnFst {α₁ α₂ : Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _} (r : α₁ → α₂ → Prop) : Sigma β₁ → Sigma β₂ → Prop :=
  λ x y => r x.fst y.fst

instance instTransOfFst {α₁ α₂ α₃ : Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _} {β₃ : α₃ → Type _} {r₁ : α₁ → α₂ → Prop} {r₂ : α₂ → α₃ → Prop} {r : α₁ → α₃ → Prop} [Trans r₁ r₂ r] : Trans (Sigma.relOnFst (β₁:=β₁) (β₂:=β₂) r₁) (Sigma.relOnFst (β₁:=β₂) (β₂:=β₃) r₂) (Sigma.relOnFst r) where
  trans := by dsimp [relOnFst]; exact trans


section Eq

variable {α : Type u} {β : α → Type v}

--- Decidability of the equality of Sigma type
instance instDecidableEqSigma [DecidableEq α] [(a : α) → DecidableEq (β a)] : DecidableEq (Sigma β) :=
  λ x y =>
    if h : x.1=y.1 then
      if h₂ : (h▸x.2) = y.2 then
        isTrue $ by
          cases x with | mk a x =>
          cases y with | mk b y =>
          dsimp at h; cases h
          dsimp at h₂; cases h₂
          rfl
      else
        isFalse $ by
          cases x with | mk a x =>
          cases y with | mk b y =>
          dsimp at h; cases h
          dsimp at *
          intro heq; cases heq
          exact absurd rfl h₂
    else
      Decidable.isFalse (λ heq => absurd (congrArg Sigma.fst heq) h)

protected
theorem eq_of_eq_snd {a : α} {b₁ b₂ : β a} : b₁ = b₂ → Sigma.mk a b₁ = Sigma.mk a b₂ :=
  λ h => h ▸ rfl

end Eq


protected
inductive lex {α : Type u} {β : α → Type v} (r : α → α → Prop) (s : (a : α) → β a → β a → Prop) : Sigma β → Sigma β → Prop
| fst {a b : α} {x : β a} {y : β b} : r a b → Sigma.lex r s ⟨a,x⟩ ⟨b,y⟩
| snd {a : α} {x y : β a} : s a x y → Sigma.lex r s ⟨a,x⟩ ⟨a,y⟩

namespace lex

variable {α : Type u} {β : α → Type v} {r : α → α → Prop} {s : (a : α) → β a → β a → Prop}

instance instDecidableRellex [DecidableEq α] [DecidableRel r] [(a : α) → DecidableRel (s a)] : DecidableRel (Sigma.lex r s)
| mk a₁ b₁, mk a₂ b₂ =>
  if hfst : r a₁ a₂ then
    isTrue $ lex.fst hfst
  else if heq : a₁ = a₂ then
    if hsnd : s a₁ b₁ (heq ▸ b₂) then
      isTrue $ heq ▸ lex.snd hsnd
    else
      isFalse $ by
        cases heq; dsimp at *
        intro h; cases h <;> contradiction
  else
    isFalse $ by
      intro hcontra; cases hcontra <;> contradiction

instance instTranslex [Trans r r r] [(a : α) → Trans (s a) (s a) (s a)] : Trans (Sigma.lex r s) (Sigma.lex r s) (Sigma.lex r s) where
  trans
  | fst hab, fst hbc => lex.fst (trans hab hbc)
  | fst hab, snd _ => lex.fst hab
  | snd _, fst hbc => lex.fst hbc
  | snd hab, snd hbc => lex.snd (trans hab hbc)

instance instIrreflectivelex [Irreflective r] [(a : α) → Irreflective (s a)] : Irreflective (Sigma.lex r s) where
  irrefl
  | mk a _, fst h => absurd h (Irreflective.irrefl a)
  | mk _ b, snd h => absurd h (Irreflective.irrefl b)

instance instAsymmetrylex [Asymmetry r] [(a : α) → Asymmetry (s a)] : Asymmetry (Sigma.lex r s) where
  asymm _ _
  | fst hab, fst hba => Asymmetry.asymm _ _ hab hba
  | fst hab, snd _ => Asymmetry.asymm _ _ hab hab
  | snd _, fst hba => Asymmetry.asymm _ _ hba hba
  | snd hab, snd hba => Asymmetry.asymm _ _ hab hba

instance instTrichotomouslex [Trichotomous r] [(a : α) → Trichotomous (s a)] : Trichotomous (Sigma.lex r s) where
  trichot
  | mk a₁ b₁, mk a₂ b₂ =>
    trichotCasesOn r (motive:=λ a₁ a₂=> ∀ (b₁ : β a₁) (b₂ : β a₂), Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂ ∨ Sigma.lex r s ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ ∨ Sigma.lex r s ⟨a₂,b₂⟩ ⟨a₁,b₁⟩) a₁ a₂
      (λ a b₁ b₂ =>
        trichotCasesOn (s a) b₁ b₂
          (λ _ => Or.inl rfl)
          (λ _ _ h => Or.inr $ Or.inl $ lex.snd h)
          (λ _ _ h => Or.inr $ Or.inr $ lex.snd h)
      )
      (λ _ _ h _ _ => Or.inr $ Or.inl $ lex.fst h)
      (λ _ _ h _ _ => Or.inr $ Or.inr $ lex.fst h)
      b₁ b₂

end lex

-- The relation `LT`
section LT

variable {α : Type u} {β : α → Type v}

--- Lexicographical ordering on the Sigma type
protected
inductive lt [LT α] [(a : α) → LT (β a)] : Sigma β → Sigma β → Prop
| fst {a b : α} {x : β a} {y : β b} : a < b → Sigma.lt ⟨a,x⟩ ⟨b,y⟩
| snd {a : α} {x y : β a} : x < y → Sigma.lt ⟨a,x⟩ ⟨a,y⟩

instance instLTSigma [LT α] [(a : α) → LT (β a)] : LT (Sigma β) where
  lt := Sigma.lt

instance sigmaHasDecidableLT [DecidableEq α] [LT α] [DecidableRel (α:=α) LT.lt] [(a : α) → LT (β a)] [(a : α) → DecidableRel (α:=β a) LT.lt] : DecidableRel (α:=Sigma β) LT.lt
| mk a₁ b₁, mk a₂ b₂ =>
  if ha : a₁ < a₂ then
    isTrue $ Sigma.lt.fst ha
  else if heq : a₁ = a₂ then
      if hb : b₁ < heq ▸ b₂ then
        isTrue $ heq ▸ Sigma.lt.snd hb
      else
        isFalse $ by
          cases heq; dsimp at *
          intro hlt; cases hlt <;> contradiction
  else
    isFalse $ by
      intro hlt; cases hlt <;> contradiction

instance instLawfulLTSigma [LawfulLT α] [(a : α) → LawfulLT (β a)] : LawfulLT (Sigma β) where
  irrefl x := by
    cases x
    intro hlt; cases hlt <;> exact absurd ‹_<_› (Irreflective.irrefl _)
  trans := by
    intro x y z hxy hyz
    cases x with | mk xa xb =>
    cases y with | mk ya yb =>
    cases z with | mk za zb =>
    cases hxy <;> cases hyz
    . exact Sigma.lt.fst (trans ‹xa < ya› ‹ya < za›)
    . exact Sigma.lt.fst ‹xa < ya›
    . exact Sigma.lt.fst ‹xa < za›
    . apply Sigma.lt.snd; exact (trans ‹xb < _› ‹_ < _›)

instance instLinearLTSigma [LinearLT α] [(a : α) → LinearLT (β a)] : LinearLT (Sigma β) where
  trichot x y := by
    cases x with | mk xa xb =>
    cases y with | mk ya yb =>
    apply trichotCasesOn (motive:=λ xa ya => ∀ (xb : β xa) (yb : β ya), Sigma.mk xa xb = ⟨ya,yb⟩ ∨ Sigma.mk xa xb < Sigma.mk ya yb ∨ Sigma.mk xa xb > ⟨ya,yb⟩) LT.lt xa ya _ _ _ xb yb
    . intro a xb yb
      apply Or.imp Sigma.eq_of_eq_snd (Or.imp Sigma.lt.snd Sigma.lt.snd)
      exact Trichotomous.trichot (α:=β a) (r:=LT.lt) xb yb
    . intro xa ya hxaya xb yb
      apply Or.inr $ Or.inl $ Sigma.lt.fst hxaya
    . intro xa ya hyaxa xb yb
      apply Or.inr $ Or.inr $ Sigma.lt.fst hyaxa

end LT

end Sigma
