/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Classes.LawfulMonad
import Dijkstra.Control.Functor.Subreg

import Algdata.Init.Logic
-- import Algdata.Control.MonadProp
import Algdata.Data.List.Basic

namespace List

--- Apply a predicator to `head` if any, or `True` otherwise
def predHead {α : Type _} (p : α → Prop) : List α → Prop
| [] => True
| (a::_) => p a

def predHead_of_predHead {α : Type _} {p q : α → Prop} : (∀ a, p a → q a) → ∀ {as : List α}, as.predHead p → as.predHead q
| _, [] => λ _ => True.intro
| hpq, (a::_) => hpq a

def relHead {α β : Type _} (r : α → β → Prop) : List α → List β → Prop
| [], _ => True
| (_::_), [] => True
| (a::_), (b::_) => r a b

@[simp]
theorem relHead_nil_left {α β : Type _} {r : α → β → Prop} {bs : List β} : relHead r [] bs = True := rfl

@[simp]
theorem relHead_nil_right {α β : Type _} {r : α → β → Prop} {as : List α} : relHead r as [] = True := by
  cases as <;> rfl

@[simp]
theorem relHead_cons_left {α β : Type _} {r : α → β → Prop} {a : α} {as : List α} {bs : List β} : relHead r (a::as) bs = predHead (r a) bs := by
  cases bs <;> rfl

@[simp]
theorem relHead_cons_right {α β : Type _} {r : α → β → Prop} {as : List α} {b : β} {bs : List β} : relHead r as (b::bs) = predHead (λ a => r a b) as := by
  cases as <;> rfl

theorem relHead_of_trans {α β γ : Type _} {r₁ : α → β → Prop} {r₂ : β → γ → Prop} {r : α → γ → Prop} [Trans r₁ r₂ r] {as : List α} {b : β} {cs : List γ} : as.predHead (λ a => r₁ a b) → cs.predHead (r₂ b) → as.relHead r cs := by
  cases as <;> cases cs <;> intros <;> try {intros; exact True.intro}
  dsimp [relHead]; dsimp [predHead] at *
  exact trans ‹r₁ _ b› ‹r₂ b _›

theorem relHead_eq_predHead_predHead {α β : Type _} {r : α → β → Prop} {as : List α} {bs : List β} : as.relHead r bs = predHead (λ b => as.predHead (flip r b)) bs := by
  cases as <;> cases bs <;> rfl


/-
protected
def runP : List Prop → Prop := foldr And True

section runP

@[simp]
theorem runP_nil : List.runP [] = True := rfl

@[simp]
theorem runP_cons_iff {p : Prop} {ps : List Prop} : List.runP (p::ps) = (p ∧ List.runP ps) :=
  rfl

@[simp]
theorem runP_append {ps qs : List Prop} : List.runP (ps ++ qs) = (List.runP ps ∧ List.runP qs) := by
  induction ps
  case nil => simp
  case cons p ps h_ind => simp [h_ind, and_assoc]

end runP

-/

section forAll

theorem predHead_of_forAll {α : Type _} {p : α → Prop} {as : List α} : as.forAll p → as.predHead p :=
  as.casesOn id (λ _ _ => And.left)

theorem forAll_map_eq {α β : Type _} (p : β → Prop) (f : α → β) {as : List α} : (as.map f).forAll p = as.forAll (p ∘ f) := by
  induction as
  case nil => exact rfl
  case cons a as h_ind =>
    dsimp [List.forAll]
    rw [h_ind]

@[simp]
theorem forAll_append {α : Type _} (p : α → Prop) {as bs : List α} : List.forAll p (as ++ bs) = (List.forAll p as ∧ List.forAll p bs) := by
  induction as
  case nil => dsimp [forAll]; rw [true_and]
  case cons _ _ h_ind => dsimp [forAll]; rw [h_ind, and_assoc]

@[simp]
theorem forAll_reverse {α : Type _} (p : α → Prop) {as : List α} : as.reverse.forAll p = as.forAll p := by
  induction as <;> simp
  -- case nil has been closed
  case cons a as h_ind =>
    dsimp [forAll]
    rw [h_ind, And.comm, and_true]

@[simp]
theorem forAll_reverseAux {α : Type _} (p : α → Prop) {as bs : List α} : List.forAll p (List.reverseAux as bs) = (as.forAll p ∧ bs.forAll p) := by
  have : reverseAux as [] = reverse as := rfl
  rw [reverseAux_eq_append, forAll_append, this, forAll_reverse]

theorem forAll_of_forAll {α : Type _} {p q : α → Prop} : (∀ a, p a → q a) → {as : List α} → List.forAll p as → List.forAll q as
| _, [], _ => True.intro
| hpq, (_::_), hp =>
  And.intro (hpq _ hp.left) $
    forAll_of_forAll hpq hp.right

end forAll


protected
def forAllRel {α β : Type _} (r : α → β → Prop) (as : List α) (bs : List β) : Prop :=
  as.forAll λ a => bs.forAll (r a)

section forAllRel

variable {α β : Type _} {r : α → β → Prop}

@[simp]
theorem forAllRel_nil_left {bs : List β} : List.forAllRel r [] bs = True := rfl

@[simp]
theorem forAllRel_cons_left {a : α} {as : List α} {bs : List β} : List.forAllRel r (a::as) bs =(List.forAll (r a) bs ∧ List.forAllRel r as bs) := by
  simp [List.forAllRel, map, cons_bind, List.forAll]

@[simp]
theorem forAllRel_nil_right {as : List α} : List.forAllRel r as [] = True := by
  induction as
  case nil => rfl
  case cons a as h_ind => dsimp [List.forAllRel, forAll] at *; rw [h_ind, true_and]

@[simp]
theorem forAllRel_cons_right {as : List α} {b : β} {bs : List β} : List.forAllRel r as (b::bs) = (List.forAll (r · b) as ∧ List.forAllRel r as bs) := by
  induction as
  case nil => dsimp [List.forAllRel, forAll]; rw[true_and]
  case cons a as h_ind =>
    rw [forAllRel_cons_left, h_ind]
    dsimp [forAll]
    conv =>
      lhs
      rw [←and_assoc (c:=List.forAllRel _ _ _), and_assoc (a:=r a b), And.comm (a:=List.forAll _ _) (b:=List.forAll _ _), ←and_assoc]
    simp [and_assoc]

@[simp]
theorem forAllRel_of_forAllRel {r₁ : α → β → Prop} : (∀ a b, r a b → r₁ a b) → {as : List α} → {bs : List β} → List.forAllRel r as bs → List.forAllRel r₁ as bs := by
  intro himp as
  induction as <;> simp; intro bs ha has
  -- case nil has been closed
  case cons a as h_ind =>
    constructor
    case left => exact List.forAll_of_forAll (himp a) ha
    case right => exact h_ind has

theorem forAllRel_of_trans_forAll_forAll {α β γ : Type _} {r₁ : α → β → Prop} {r₂ : β → γ → Prop} {r : α → γ → Prop} [Trans r₁ r₂ r] {as : List α} {b : β} {cs : List γ} : as.forAll (r₁ · b) → cs.forAll (r₂ b) → List.forAllRel r as cs := by
  induction as <;> simp
  -- case nil has been closed
  case cons a as h_ind =>
    dsimp [List.forAllRel, forAll]
    intro habsb hbc
    constructor
    case left =>
      exact forAll_of_forAll (λ c (h : r₂ b c) => trans habsb.left h) hbc
    case right =>
      exact h_ind habsb.right hbc

theorem forAllRel_trans {α β γ : Type _} {r₁ : α → β → Prop} {r₂ : β → γ → Prop} {r : α → γ → Prop} [Trans r₁ r₂ r ] {as : List α} {bs : List β} {cs : List γ} : bs ≠ [] → List.forAllRel r₁ as bs → List.forAllRel r₂ bs cs → List.forAllRel r as cs := by
  intro hbs hab hbc
  cases bs
  case nil => exact absurd rfl hbs
  case cons b bs =>
    simp at hab hbc
    exact forAllRel_of_trans_forAll_forAll hab.left hbc.left

@[simp]
theorem forAllRel_flip {as : List α} {bs : List β} : List.forAllRel (flip r) bs as = List.forAllRel r as bs := by
  induction as <;> simp
  -- case nil has been closed
  case cons a as h_ind =>
    rw [h_ind]; exact And.substIff Iff.rfl Iff.rfl

@[simp]
theorem forAllRel_reverse_left {as : List α} {bs : List β} : List.forAllRel r as.reverse bs = List.forAllRel r as bs := by
  induction bs generalizing as <;> simp
  -- case nil has been closed.
  case cons _ _ h_ind =>
    rw [h_ind]; intros; exact Iff.rfl

@[simp]
theorem forAllRel_reverse_right {as : List α} {bs : List β} : List.forAllRel r as bs.reverse = List.forAllRel r as bs:= by
  rw [←forAllRel_flip, ←forAllRel_flip (r:=r)]
  exact forAllRel_reverse_left

end forAllRel

end List
