/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
 
import Algdata.Data.Subtype.Basic
import Algdata.Control.Lawful

universe u v

@[unbox]
structure PProof : Type u where
  target : Prop
  proof : target

protected
def PProof.and : PProof → PProof → PProof :=
  λ x y => ⟨x.target ∧ y.target, And.intro x.proof y.proof⟩

protected
def PProof.true : PProof :=
  ⟨True, True.intro⟩

def runP {f : Type → Type v} [Functor f] (fp : f Prop) : Prop :=
  ∃ (prf : f PProof), PProof.target <$> prf = fp

def p (c : Nat → Sort u) : Prop := ∀ n, ∀ (a : c n), a = a

theorem runP_pure_of_true {f : Type _ → Type v} [Applicative f] [LawfulApplicative f] (p : Prop) : p →  runP (f:=f) (pure p) :=
  λ hp => Exists.intro (pure ⟨p,hp⟩) (map_pure (f:=f) PProof.target _ ▸ rfl)

theorem runP_And {f : Type _ → Type _} [Applicative f] [LawfulApplicative f] (fp fq : f Prop) : runP fp → runP fq → runP (And <$> fp <*> fq) := by
  intro hfp hfq
  cases hfp with | intro hfp hp =>
  cases hfq with | intro hfq hq =>
  exists PProof.and <$> hfp <*> hfq
  rw [←hp, ←hq]
  rw [←comp_map, map_seq]
  rw [←pure_seq, ←pure_seq, ←pure_seq, seq_assoc]
  rw [seq_pure, pure_seq, ←comp_map, pure_seq, ←comp_map]
  dsimp [PProof.and, Function.comp]


namespace Option

theorem runP_none : runP none :=
  ⟨none, rfl⟩

theorem runP_some {p : Prop} : runP (some p) ↔ p where
  mp hrunP := hrunP.casesOn $ λ oprf h => by
    cases oprf <;> dsimp [Functor.map, Option.map] at h
    case none =>
      cases h
    case some prf =>
      have := Option.some.inj h
      exact this ▸ prf.proof
  mpr hp := ⟨some ⟨p,hp⟩,rfl⟩

end Option


def mapP {f : Type _ → Type _} [Functor f] {α : Type _} : (α → Prop) → f α → Prop :=
  fun p x => ∃ (w : f (Subtype p)), x = Subtype.val <$> w

infixr:100 " <$? " => mapP

theorem mapP_map_of_comp_mapP {f : Type _ → Type _} [Functor f] [LawfulFunctor f] {α β : Type _} {p : β → Prop} {g : α → β} : ∀ (x : f α), mapP (p ∘ g) x → mapP p (g <$> x) := by
  intro x hx
  cases hx with | intro w hw =>
  cases hw
  exists Subtype.push g <$> w
  rw [←comp_map, ←comp_map]
  apply map_congr
  intro a
  simp

theorem mapP_imp {f : Type _ → Type _} [Functor f] [LawfulFunctor f] {α : Type _} {p q : α → Prop} : (∀ a, p a → q a) → ∀ (x : f α), mapP p x → mapP q x := by
  intro hpq x hpx
  cases hpx with | intro w hw =>
  exists Subtype.translate hpq <$> w
  rw [←comp_map]
  have : Subtype.val (p:=q) ∘ Subtype.translate hpq = Subtype.val (p:=p) :=
    funext $ Subtype.val_translate hpq
  rw [this]
  exact hw

theorem mapP_of_pure {f : Type _ → Type _} [Applicative f] [LawfulApplicative f] {α : Type _} {p : α → Prop} (a : α) : p a → mapP p (pure (f:=f) a) := by
  intros ha
  exists pure (f:=f) $ Subtype.mk (p:=p) a ha
  rw [map_pure]

