/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Order
import Algdata.Init.LawfulLT
import Algdata.Data.List.Basic
import Algdata.Data.KVChain.Basic
import Algdata.Data.KVChain.MergeWith
import Algdata.Algebra.Monoid.FreeCMonoid


/-!

# Monomial order

Given a (decidable) linearly ordered type `α`, a relation `r : FreeCMonoid α → FreeCMonoid α → Prop` is called a monomial order if it satisfies the following:

  - it is a strict linear order
  - `1` is minimum; i.e. `¬ r 1 x` implies `x=1`
  - it is stable under the right translation; i.e. `r x y` implies `r (x*z) (y*z)`

@remark We always assume decidability.
-/

universe u

structure MonomialOrder (α : Type u) [LinearLT α] [DecidableRel (α:=α) LT.lt] where
  lt : FreeCMonoid α → FreeCMonoid α → Prop
  linear : StrictLinearOrder lt
  decidable : DecidableRel lt
  unit_antisymm : ∀ x, ¬ lt 1 x → x = 1
  mul_lt_mul_right : ∀ (x y z : FreeCMonoid α), lt x y → lt (x*z) (y*z)

attribute [instance] MonomialOrder.linear
attribute [instance] MonomialOrder.decidable

namespace MonomialOrder

variable {α : Type u} [DecidableEq α] [LinearLT α] [DecidableRel (α:=α) LT.lt]


protected
def gt (o : MonomialOrder α) : FreeCMonoid α → FreeCMonoid α → Prop :=
  flip o.lt

instance (o : MonomialOrder α) : StrictLinearOrder o.gt :=
  inferInstanceAs (StrictLinearOrder (flip o.lt))

instance (o : MonomialOrder α) : DecidableRel o.gt :=
  inferInstanceAs (DecidableRel (flip o.lt))

theorem mul_lt_mul_left (o : MonomialOrder α) : ∀ (x y z : FreeCMonoid α), o.lt x y → o.lt (z*x) (z*y) :=
    λ x y z => 
      FreeCMonoid.mul_comm x z ▸ FreeCMonoid.mul_comm y z ▸ o.mul_lt_mul_right x y z


--- Purely lexicographical order
@[inline]
def plex : MonomialOrder α where
  lt := InvImage (KVChain.rklex (λ _=>LT.lt)) FreeCMonoid.vars
  linear := {
    toTrans := inferInstance
    toIrreflective := inferInstance
    toTrichotomous := mkInstTrichotomousInvImage _ FreeCMonoid.vars $ @FreeCMonoid.eq _ _
  }
  decidable := inferInstance
  unit_antisymm x h := by
    cases x with | mk xv =>
    cases xv with | mk toList chain =>
    dsimp [OfNat.ofNat] at *
    cases toList
    case nil => rfl
    case cons x xs =>
      exact absurd (List.lex.nil x xs) h
  mul_lt_mul_right
  | FreeCMonoid.mk xvars, FreeCMonoid.mk yvars, FreeCMonoid.mk zvars => by
    unfold InvImage
    dsimp [HMul.hMul, Mul.mul]
    apply KVChain.rklex_mergeWith_right
    case hsf_right =>
      intro _ b₁ b
      cases b₁ with | mk m m_gt_zero =>
      cases b with | mk n n_gt_zero =>
      dsimp [LT.lt, FreeCMonoid.valAdd]
      unfold InvImage; dsimp
      calc
        m = 0 + m := (Nat.zero_add m).symm
        _ < n + m := Nat.add_lt_add_right n_gt_zero _
    case hsf_stab =>
      intro _ b₁ b₂ b hb₁b₂
      cases b₁ with | mk m₁ m₁_gt_zero =>
      cases b₂ with | mk m₂ m₂_gt_zero =>
      cases b with | mk n n_gt_zero =>
      dsimp [LT.lt, FreeCMonoid.valAdd]
      unfold InvImage; dsimp
      exact Nat.add_lt_add_right hb₁b₂ n

--- Degree-wise lexicographical order
@[inline]
def deglex : MonomialOrder α where
  lt := Lexcomb (InvImage Nat.lt FreeCMonoid.degree) plex.lt
  linear := inferInstance
  decidable := inferInstance
  unit_antisymm x h := by
    cases Nat.eq_zero_or_pos x.degree
    case inl hx => exact FreeCMonoid.eq_one_of_degree_zero hx
    case inr hx => exact absurd (Or.inl hx) h
  mul_lt_mul_right x y z hxy := by
    unfold InvImage at *
    cases hxy
    case inl hdeg =>
      apply Or.inl; dsimp at *
      rw [FreeCMonoid.degree_mul, FreeCMonoid.degree_mul]
      exact Nat.add_lt_add_right hdeg _
    case inr hxy =>
      apply Or.inr
      constructor
      case left =>
        unfold Incomp at *; dsimp at *
        have : x.degree = y.degree := Trichotomous.eq_of_incomp hxy.left
        rw [FreeCMonoid.degree_mul, FreeCMonoid.degree_mul, this]
        exact ⟨Nat.lt_irrefl _, Nat.lt_irrefl _⟩
      case right =>
        exact plex.mul_lt_mul_right x y z hxy.right

--- @todo Complete the proof that `devrevlex` is a monomial order.
@[inline]
def degrevlex : MonomialOrder α where
  lt := Lexcomb (InvImage Nat.lt FreeCMonoid.degree) (InvImage (KVChain.rklex (λ _=>LT.lt)) (KVChain.reverse ∘ FreeCMonoid.vars))
  linear := {
    toTrans := inferInstance
    toIrreflective := inferInstance
    toTrichotomous := sorry
  }
  decidable := inferInstance
  unit_antisymm := sorry
  mul_lt_mul_right := sorry

end MonomialOrder
