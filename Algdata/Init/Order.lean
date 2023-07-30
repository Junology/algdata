/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic

section Order

universe u

variable {α : Type u}

/-
  Indivisual axioms
-/
class Irreflective (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ r a a

class Asymmetry (r : α → α → Prop) : Prop where
  asymm : ∀ a b, r a b → ¬ r b a

instance instIrreflectiveAsymmetry (r : α → α → Prop) [Asymmetry r] : Irreflective r where
  irrefl _ haa := absurd haa (Asymmetry.asymm _ _ haa)

instance instAsymmetryIrreflectiveTrans (r : α → α → Prop) [Trans r r r] [Irreflective r] : Asymmetry r where
  asymm _ _ hab hba := Irreflective.irrefl _ (trans hab hba)


@[inline, reducible]
def Incomp (r : α → α → Prop) (a b : α) : Prop :=
  ¬ r a b ∧ ¬ r b a

protected
theorem Incomp.symm {r : α → α → Prop} {a b : α} : Incomp r a b → Incomp r b a :=
  And.comm.mp

class IncompStable (r : α → α → Prop) : Prop where
  stable_left : ∀ a b c, Incomp r a b → r b c → r a c
  stable_right : ∀ a b c, r a b → Incomp r b c → r a c

instance instTransIncomp (r : α → α → Prop) [Trans r r r] [IncompStable r] : Trans (Incomp r) (Incomp r) (Incomp r) where
  trans {a b c} hab hbc := by
    apply And.intro
    . intro hac
      have := IncompStable.stable_right _ _ _ hac hbc.symm
      exact absurd this hab.left
    . intro hca
      have := IncompStable.stable_right _ _ _ hca hab
      exact absurd this hbc.right


class Trichotomous (r : α → α → Prop) : Prop where
  trichot : ∀ a b, a = b ∨ r a b ∨ r b a

theorem Trichotomous.eq_of_incomp {r : α → α → Prop} [Trichotomous r] {a b : α} : Incomp r a b → a = b :=
  λ hincomp => (trichot a b).elim id (Or.rec (flip absurd hincomp.left) (flip absurd hincomp.right))

instance instIncompStableTrichotomous (r : α → α → Prop) [Trichotomous r] : IncompStable r where
  stable_left _ _ _ hab hbc := (Trichotomous.eq_of_incomp hab) ▸ hbc
  stable_right _ _ _ hab hbc := (Trichotomous.eq_of_incomp hbc) ▸ hab

@[elab_as_elim]
theorem trichot_cases {motive : α → α → Prop} (r : α → α → Prop) [Trichotomous r] (of_rfl : ∀ a, motive a a) (of_rel : ∀ a b, r a b → motive a b) (of_opp : ∀ a b, r b a → motive a b) : ∀ (a b : α), motive a b :=
  λ a b =>
    match Trichotomous.trichot (r:=r) a b with
    | Or.inl h => h ▸ of_rfl a
    | Or.inr (Or.inl h) => of_rel a b h
    | Or.inr (Or.inr h) => of_opp a b h

@[elab_as_elim, reducible]
theorem trichot_cases_on {motive : α → α → Prop} (r : α → α → Prop) [Trichotomous r] (a b: α) (of_rfl : ∀ a, motive a a) (of_rel : ∀ a b, r a b → motive a b) (of_opp : ∀ a b, r b a → motive a b) : motive a b :=
  trichot_cases r of_rfl of_rel of_opp a b

@[elab_as_elim, inline, reducible]
def decTrichotCases {motive : α → α → Sort _} (r : α → α → Prop) [Trichotomous r] [DecidableRel r] (of_rfl : ∀ a, motive a a) (of_rel : ∀ a b, r a b → motive a b) (of_opp : ∀ a b, r b a → motive a b) : (a b : α) → motive a b :=
  λ a b => dite (r a b) (of_rel _ _) (λ hab => dite (r b a) (of_opp _ _) (λ hba => Trichotomous.eq_of_incomp ⟨hab,hba⟩ ▸ of_rfl a))

@[elab_as_elim, inline, reducible]
def decTrichotCasesOn {motive : α → α → Sort _} (r : α → α → Prop) [Trichotomous r] [DecidableRel r] (a b : α) (of_rfl : ∀ a, motive a a) (of_rel : ∀ a b, r a b → motive a b) (of_opp : ∀ a b, r b a → motive a b) : motive a b :=
  decTrichotCases r of_rfl of_rel of_opp a b


/-
  Strict orders
-/
class StrictOrder (r : α  → α → Prop) extends Trans r r r, Irreflective r

attribute [instance] StrictOrder.mk

class StrictLinearOrder (r : α → α → Prop) extends StrictOrder r, Trichotomous r

attribute [instance] StrictLinearOrder.mk


/-
  Constructions
-/
-- opposite order
instance (r : α → α → Prop) [Trans r r r] : Trans (flip r) (flip r) (flip r) where
  trans := flip (trans (r:=r))

instance (r : α → α → Prop) [Irreflective r] : Irreflective (flip r) where
  irrefl := Irreflective.irrefl (r:=r)

instance (r : α → α → Prop) [Asymmetry r] : Asymmetry (flip r) where
  asymm a b := Asymmetry.asymm b a

instance (r : α → α → Prop) [IncompStable r] : IncompStable (flip r) where
  stable_left _ _ _ hab hbc := IncompStable.stable_right (r:=r) _ _ _ hbc hab
  stable_right _ _ _ hab hbc := IncompStable.stable_left (r:=r) _ _ _ hbc hab

instance (r : α → α → Prop) [Trichotomous r] : Trichotomous (flip r) where
  trichot a b := Or.imp Eq.symm id $ Trichotomous.trichot (r:=r) b a

#print Or
instance (r : α → α → Prop) [DecidableRel r] : DecidableRel (flip r) :=
  λ a b => inferInstanceAs (Decidable (r b a))

-- inverse image of relation
-- `InvImage` defined in `Init.Core` in Lean4
instance {β : Type _} (r : α → α → Prop) [Trans r r r] (f : β → α) : Trans (InvImage r f) (InvImage r f) (InvImage r f) where
  trans hab hbc := trans (r:=r) hab hbc

instance {β : Type _} (r : α → α → Prop) [Irreflective r] (f : β → α) : Irreflective (InvImage r f) where
  irrefl a := Irreflective.irrefl (f a)

instance {β : Type _} (r : α → α → Prop) [Asymmetry r] (f : β → α) : Asymmetry (InvImage r f) where
  asymm a b := Asymmetry.asymm (f a) (f b)

instance {β : Type _} (r : α → α → Prop) [IncompStable r] (f : β → α) : IncompStable (InvImage r f) where
  stable_left a b c := IncompStable.stable_left (f a) (f b) (f c)
  stable_right a b c := IncompStable.stable_right (f a) (f b) (f c)

instance {β : Type _} (r : α → α → Prop) [DecidableRel r] (f : β → α) : DecidableRel (InvImage r f) :=
  λ a b => dite (r (f a) (f b)) isTrue isFalse

def mkInstTrichotomousInvImage {β : Type _} (r : α → α → Prop) [Trichotomous r] (f : β → α) (f_inj : ∀ b₁ b₂, f b₁ = f b₂ → b₁ = b₂) : Trichotomous (InvImage r f) where
  trichot b₁ b₂ :=
    Or.imp (f_inj b₁ b₂) id $ Trichotomous.trichot (f b₁) (f b₂)


--- Lexicographical combination of two relations
@[inline, reducible]
def Lexcomb (r s : α → α → Prop) (a b : α) : Prop :=
  r a b ∨ (Incomp r a b ∧ s a b)

instance (r s : α → α → Prop) [DecidableRel r] [DecidableRel s] : DecidableRel (Lexcomb r s) :=
  λ _ _ => inferInstance

instance (r s : α → α → Prop) [Trans r r r] [IncompStable r] [Trans s s s] : Trans (Lexcomb r s) (Lexcomb r s) (Lexcomb r s) where
  trans
  | Or.inl hrab, Or.inl hrbc => Or.inl (trans hrab hrbc)
  | Or.inl hrab, Or.inr hsbc => Or.inl (IncompStable.stable_right _ _ _ hrab hsbc.left)
  | Or.inr hsab, Or.inl hrbc => Or.inl (IncompStable.stable_left _ _ _ hsab.left hrbc)
  | Or.inr hsab, Or.inr hsbc => Or.inr ⟨trans hsab.left hsbc.left, trans hsab.right hsbc.right⟩

instance (r s : α → α → Prop) [Irreflective r] [Irreflective s] : Irreflective (Lexcomb r s) where
  irrefl a
  | Or.inl hraa => absurd hraa (Irreflective.irrefl (r:=r) a)
  | Or.inr hsaa => absurd hsaa.right (Irreflective.irrefl (r:=s) a)

instance (r s : α → α → Prop) [Asymmetry r] [Asymmetry s] : Asymmetry (Lexcomb r s) where
  asymm _ _
  | Or.inl hrab, Or.inl hrba => Asymmetry.asymm _ _ hrab hrba
  | Or.inl hrab, Or.inr hsba => absurd hrab hsba.left.right
  | Or.inr hsab, Or.inl hrba => absurd hrba hsab.left.right
  | Or.inr hsab, Or.inr hsba => Asymmetry.asymm _ _ hsab.right hsba.right

@[simp]
theorem Incomp_Lexcomb_iff {r s : α → α → Prop} {a b : α}: Incomp (Lexcomb r s) a b ↔ Incomp r a b ∧ Incomp s a b where
  mp h := by
    dsimp [Incomp] at h
    have hab := not_or.mp h.left
    have hba := not_or.mp h.right
    have : Incomp r a b := ⟨hab.left, hba.left⟩
    have hsab : ¬ s a b :=
      λ h => absurd ⟨this, h⟩ hab.right
    have hsba : ¬ s b a :=
      λ h => absurd ⟨this.symm, h⟩ hba.right
    exact ⟨this, ⟨hsab, hsba⟩⟩
  mpr h := by
    unfold Incomp
    dsimp [Lexcomb]
    apply And.intro <;> apply not_or.mpr
    case left =>
      exact ⟨h.left.left, h.right.left ∘ And.right⟩
    case right =>
      exact ⟨h.left.right, h.right.right ∘ And.right⟩

instance (r s : α → α → Prop) [Trans r r r] [IncompStable r] [IncompStable s] : IncompStable (Lexcomb r s) where
  stable_left a b c := by
    intro hab hbc
    have := Incomp_Lexcomb_iff.mp hab
    cases hbc with
    | inl hrbc => exact Or.inl (IncompStable.stable_left _ _ _ this.left hrbc)
    | inr hsbc =>
      apply Or.inr; apply And.intro
      . exact trans this.left hsbc.left
      . exact IncompStable.stable_left _ _ _ this.right hsbc.right
  stable_right a b c := by
    intro hab hbc
    have := Incomp_Lexcomb_iff.mp hbc
    cases hab with
    | inl hrab => exact Or.inl (IncompStable.stable_right _ _ _ hrab this.left)
    | inr hsab =>
      apply Or.inr; apply And.intro
      . exact trans hsab.left this.left
      . exact IncompStable.stable_right _ _ _ hsab.right this.right

instance (r s : α → α → Prop) [DecidableRel r] [Trichotomous s] : Trichotomous (Lexcomb r s) where
  trichot a b :=
    if hab : r a b then
      Or.inr $ Or.inl $ Or.inl hab
    else if hba : r b a then
      Or.inr $ Or.inr $ Or.inl hba
    else
      trichot_cases_on s a b
        (λ _ _ => Or.inl rfl)
        (λ _ _ hsab hrab => Or.inr $ Or.inl $ Or.inr ⟨hrab,hsab⟩)
        (λ _ _ hsba hrab => Or.inr $ Or.inr $ Or.inr ⟨⟨hrab.right,hrab.left⟩, hsba⟩)
        (And.intro hab hba)


/-
  Instances on some buit-in types
-/
instance instStrictLinearOrderNatLT : StrictLinearOrder Nat.lt where
  trans := Nat.lt_trans
  irrefl := Nat.lt_irrefl
  trichot a b :=
    match Nat.lt_or_ge a b with
    | Or.inl h =>  Or.inr (Or.inl h)
    | Or.inr h =>
      match Nat.eq_or_lt_of_le h with
      | Or.inl h => Or.inl h.symm
      | Or.inr h => Or.inr (Or.inr h)

instance instStrictLinearOrderNatGT : StrictLinearOrder (α:=Nat) GT.gt where
  trans := flip Nat.lt_trans
  irrefl := Nat.lt_irrefl
  trichot a b :=
    match Trichotomous.trichot (r:=Nat.lt) b a with
    | Or.inl h => Or.inl h.symm
    | Or.inr h => Or.inr h

end Order