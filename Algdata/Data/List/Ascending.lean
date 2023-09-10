/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.LawfulLT
import Algdata.Data.List.Basic
import Algdata.Data.List.Prop

namespace List

universe u
/-
  Property of lists that every pair of consequtive entries satisfies a specified condition.
-/
inductive Ascending {α : Type u} (r : α → α → Prop) : List α → Prop
| nil : Ascending r []
| singleton (a : α) : Ascending r [a]
| cons {a b : α} {bs : List α} : r a b → Ascending r (b::bs) → Ascending r (a::b::bs)

namespace Ascending

variable {α : Type u} {r : α → α → Prop}

protected
theorem tail {a : α} {as : List α} : Ascending r (a::as) → Ascending r as
| singleton _ => Ascending.nil
| cons _ h => h

protected
theorem head {a : α} {as : List α} : Ascending r (a::as) → as.predHead (r a) := by
  intro hchain; cases hchain
  case singleton => exact True.intro
  case cons => exact ‹r a _›

theorem of_implies {r₁ : α → α → Prop} : (∀ a b, r a b → r₁ a b) → {as : List α} → Ascending r as → Ascending r₁ as
| _, _, nil => Ascending.nil
| _, _, singleton a => Ascending.singleton a
| himp, _, cons ha has => Ascending.cons (himp _ _ ha) (of_implies himp has)

theorem of_append_left {as bs : List α} : Ascending r (as++bs) → Ascending r as := by
  induction as
  case nil => exact λ _ => Ascending.nil
  case cons a as h_ind =>
    cases as
    case nil => exact λ _ => Ascending.singleton a
    case cons a₁ as =>
      simp [List.cons_append] at *
      intro has; cases has with | cons ha htail =>
      exact Ascending.cons ha (h_ind htail)

theorem of_append_right {as bs : List α} : Ascending r (as++bs) → Ascending r bs := by
  induction as
  case nil => exact id
  case cons _ _ h_ind => exact h_ind ∘ Ascending.tail

theorem predHead_tail {a : α} {as : List α} {p : α → Prop} : (∀ a b, p a → r a b → p b) → Ascending r (a::as) → (a::as).predHead p → as.predHead p := by
  intro hup hchain hpa
  cases as
  case nil => exact True.intro
  case cons a₁ as => exact hup a a₁ hpa hchain.head

theorem forAll_of_tail [Trans r r r] {a : α} {as : List α} : Ascending r (a::as) → as.forAll (r a) := by
  revert a
  induction as <;> intro a h
  case nil => exact True.intro
  case cons a₁ as h_ind =>
    cases h with | cons ha htail =>
    have : as.forAll (r a) :=
      forAll_of_forAll (λ x => trans ha) $ h_ind htail
    exact And.intro ha this

theorem forAll_of_predHead {p : α → Prop} {as : List α} : (∀ a b, p a → r a b → p b) → as.predHead p → as.Ascending r → as.forAll p := by
  induction as
  case nil => intros; exact True.intro
  case cons a as h_ind =>
    intro hup hpa hchain
    exact ⟨hpa, h_ind hup (hchain.predHead_tail hup hpa) hchain.tail⟩

theorem forAllRel_of_append [Trans r r r] {as bs : List α} : Ascending r (as++bs) → List.forAllRel r as bs := by
  induction as <;> simp
  -- case nil has been closed
  case cons a as h_ind =>
    intro hass
    have := hass.forAll_of_tail; simp at this
    exact And.intro this.right (h_ind hass.tail)

theorem cons_of_head_tail {a : α} {as : List α} : as.predHead (r a) → as.Ascending r → Ascending r (a::as) := by
  cases as
  case nil => exact λ _ _ => Ascending.singleton _
  case cons => exact Ascending.cons

theorem cons_of_forAll {a : α} {as : List α} : as.forAll (r a) → Ascending r as → Ascending r (a::as) := by
  cases as
  case nil => intros; exact Ascending.singleton a
  case cons a₁ as =>
    intro h
    exact Ascending.cons h.left

theorem append [Trans r r r] {as bs : List α} : List.forAllRel r as bs →  Ascending r as → Ascending r bs → Ascending r (as ++ bs) := by
  induction as
  case nil => dsimp; exact λ _ _ => id
  case cons a as h_ind =>
    dsimp [forAllRel_cons_left]
    rw [List.forAllRel_cons_left]
    intro h hass hbs
    have htail := h_ind h.right hass.tail hbs
    have hhead : bs.forAll (r a) := h.left
    apply cons_of_forAll _ htail
    rw [forAll_append]
    exact And.intro hass.forAll_of_tail hhead

protected
theorem map.{v} {β : Type v} (r' : β → β → Prop) (f : α → β) (rel_pres : ∀ a₁ a₂, r a₁ a₂ → r' (f a₁) (f a₂)) : ∀ {as : List α}, as.Ascending r → (as.map f).Ascending r'
| [], _ => Ascending.nil
| [a], Ascending.singleton _ => Ascending.singleton (f a)
| (_::_::_), Ascending.cons h hs => Ascending.cons (rel_pres _ _ h) $ hs.map r' f rel_pres

protected
theorem reverseAux_cons {a : α} {as bs : List α} : Ascending (flip r) (a::as) → Ascending r (a::bs) → Ascending r (List.reverseAux (a::as) bs) := by
  revert a bs; induction as <;> dsimp [reverseAux] <;> intro a bs
  case nil => exact λ _ => id
  case cons a' as h_ind =>
    intro haaas habs
    simp [reverseAux] at h_ind
    cases haaas with | cons haa haas =>
    apply h_ind haas (habs.cons haa)

theorem reverseAux {as bs : List α} : List.relHead r as bs → Ascending (flip r) as → Ascending r bs → Ascending r (reverseAux as bs) := by
  revert bs; induction as <;> intro bs
  case nil => exact λ _ _ => id
  case cons a as h_ind =>
    intro hhead has hbs
    unfold List.reverseAux
    apply h_ind
    . exact relHead_cons_right ▸ has.head
    . exact has.tail
    . exact hbs.cons_of_head_tail (relHead_cons_left ▸ hhead)

protected
theorem reverse {as : List α} : Ascending r as → Ascending (flip r) as.reverse :=
  λ hchain =>
    have : Ascending (flip (flip r)) as :=
      hchain.of_implies λ _ _ => id
    reverseAux (as:=as) (bs:=[]) (by cases as <;> exact True.intro) this Ascending.nil

protected
theorem subst_head {a b : α} (hab : ∀ c, r a c → r b c) : {as : List α} → Ascending r (a::as) → Ascending r (b::as)
| _, singleton _ => Ascending.singleton _
| _, cons ha' has => Ascending.cons (hab _ ha') has

protected
theorem filterMap.{v} [Trans r r r] {β : Type v} (r' : β → β → Prop) (f : α → Option β) (rel_pres : ∀ a₁ a₂, r a₁ a₂ → ∀ b₁ b₂, f a₁ = some b₁ → f a₂ = some b₂ → r' b₁ b₂) : ∀ {as : List α}, as.Ascending r → (as.filterMap f).Ascending r' := by
  intro as; induction as
  case nil => exact λ _ => Ascending.nil
  case cons a as h_ind =>
    intro hchain
    unfold filterMap
    cases hfa : f a <;> dsimp
    case none => exact h_ind hchain.tail
    case some b =>
      apply cons_of_forAll
      . clear h_ind
        induction as <;> dsimp [filterMap]
        case a.nil => dsimp [List.forAll]
        case a.cons a₁ as h_ind₁ =>
          have hchainaas : Ascending r (a::as) := by
            apply hchain.tail.subst_head
            exact λ _ h => trans hchain.head h
          cases hfa₁ : f a₁ <;> dsimp
          case none => exact h_ind₁ hchainaas
          case some b₁ =>
            constructor
            . have := rel_pres a a₁ hchain.head
              rw [hfa, hfa₁] at this
              exact this b b₁ rfl rfl
            . exact h_ind₁ hchainaas
      . exact h_ind hchain.tail

end Ascending

/-!
  Pair `(fst,snd)` of lists such that
    - `fst` is a reversed chain
    - `snd` is a chain
    - `fst.reverse ++ snd` is a chain
-/
structure HookedAscending {α : Type _} (r : α → α → Prop) (as bs : List α) : Prop where
  fst_lt_snd : List.forAllRel r as bs
  fst_revAscending : as.Ascending (flip r)
  snd_Ascending : bs.Ascending r

namespace HookedAscending

variable {α : Type _} {r : α → α → Prop}

protected
theorem inl {as : List α} (has : as.Ascending (flip r)) : HookedAscending r as [] where
  fst_lt_snd := by simp
  fst_revAscending := has
  snd_Ascending := List.Ascending.nil

protected
theorem inr {bs : List α} (hbs : bs.Ascending r) : HookedAscending r [] bs where
  fst_lt_snd := by simp
  fst_revAscending := List.Ascending.nil
  snd_Ascending := hbs

theorem of_implies {r₁ : α → α → Prop} : (∀ a b, r a b → r₁ a b) → {as bs : List α} → HookedAscending r as bs → HookedAscending r₁ as bs := by
  intro himp as bs hhook
  constructor
  case fst_lt_snd =>
    exact List.forAllRel_of_forAllRel himp hhook.fst_lt_snd
  case fst_revAscending =>
    have : ∀ a b, flip r a b → flip r₁ a b := λ a b => himp b a
    exact hhook.fst_revAscending.of_implies this
  case snd_Ascending =>
    exact hhook.snd_Ascending.of_implies himp

protected
theorem unhook {as bs : List α} : HookedAscending r as bs → Ascending r (as.reverseAux bs) := by
  cases as <;> simp
  case nil => exact HookedAscending.snd_Ascending
  case cons a as =>
    intro hhook
    apply Ascending.reverseAux_cons
    . exact hhook.fst_revAscending
    . apply Ascending.cons_of_forAll _ hhook.snd_Ascending
      have := hhook.fst_lt_snd
      rw [List.forAllRel_cons_left] at this
      exact this.left

protected
theorem flip {as bs : List α} (hhook : HookedAscending r as bs) : HookedAscending (flip r) bs as where
  fst_lt_snd := by simp; exact hhook.fst_lt_snd
  fst_revAscending := by
    have : ∀ a b, r a b → flip (flip r) a b := λ _ _ => id
    apply Ascending.of_implies this
    exact hhook.snd_Ascending
  snd_Ascending := hhook.fst_revAscending

theorem reelL [Trans r r r] {as : List α} {b : α} {bs : List α} : HookedAscending r as (b::bs) → HookedAscending r (b::as) bs := by
  intro hhook
  have hlt := hhook.fst_lt_snd
  rw [List.forAllRel_cons_right] at hlt
  constructor
  case fst_lt_snd =>
    constructor
    case left => exact hhook.snd_Ascending.forAll_of_tail
    case right => exact hlt.right
  case fst_revAscending =>
    exact List.Ascending.cons_of_forAll hlt.left hhook.fst_revAscending
  case snd_Ascending => exact hhook.snd_Ascending.tail

theorem reelR [Trans r r r] {a : α} {as bs : List α} : HookedAscending r (a::as) bs → HookedAscending r as (a::bs) :=
  λ hhook =>
    have : Trans (flip r) (flip r) (flip r) :=
      Trans.mk (by simp [flip]; exact flip trans)
    hhook.flip.reelL.flip

theorem substToL [Trans r r r] {eqv : α → α → Prop} [Trans eqv r r] [Trans r eqv r] {a b : α} {as bs : List α} : eqv a b → eqv b a → HookedAscending r as (b::bs) → HookedAscending r (a::as) bs := by
  intro hab hba hhook
  have hlt := hhook.fst_lt_snd
  rw [List.forAllRel_cons_right] at hlt
  constructor
  case fst_lt_snd =>
    constructor
    case left =>
      apply List.forAll_of_forAll (λ x (h : r b x) => trans hab h)
      exact hhook.snd_Ascending.forAll_of_tail
    case right => exact hlt.right
  case fst_revAscending =>
    apply List.Ascending.cons_of_forAll _ hhook.fst_revAscending
    apply List.forAll_of_forAll (λ x (h : r x b) => trans h hba)
    exact hlt.left
  case snd_Ascending => exact hhook.snd_Ascending.tail

theorem consL {a : α} {as bs : List α} : as.forAll (r · a) → bs.forAll (r a) → HookedAscending r as bs → HookedAscending r (a::as) bs := by
  intro has hbs hhook
  constructor
  case fst_lt_snd =>
    simp [List.forAllRel_cons_left]
    exact And.intro hbs hhook.fst_lt_snd
  case fst_revAscending =>
    exact List.Ascending.cons_of_forAll has hhook.fst_revAscending
  case snd_Ascending => exact hhook.snd_Ascending

theorem consR {as : List α} {b : α} {bs : List α} : as.forAll (r · b) → bs.forAll (r b) → HookedAscending r as bs → HookedAscending r as (b::bs) := by
  intro has hbs hhook
  have : ∀ a b, flip (flip r) a b → r a b := λ _ _ => id
  exact (hhook.flip.consL hbs has).flip.of_implies this

theorem tailL [Trans r r r] {a : α} {as bs : List α} : HookedAscending r (a::as) bs → HookedAscending r as bs := by
  intro hhook
  constructor
  case fst_lt_snd =>
    have := hhook.fst_lt_snd
    simp [List.forAllRel_cons_left] at this
    exact this.right
  case fst_revAscending => exact hhook.fst_revAscending.tail
  case snd_Ascending => exact hhook.snd_Ascending

theorem tailR [Trans r r r] {as : List α} {b : α} {bs : List α} : HookedAscending r as (b::bs) → HookedAscending r as bs := by
  intro hhook
  have : Trans (flip r) (flip r) (flip r) :=
    Trans.mk (by simp [flip]; exact flip trans)
  exact hhook.flip.tailL.flip

end HookedAscending

end List
