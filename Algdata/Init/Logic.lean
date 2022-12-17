/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic

theorem not_or_iff_and_not {p q : Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q where
  mp := by
    intro hnpq
    constructor
    case left =>
      exact hnpq ∘ Or.inl
    case right =>
      exact hnpq ∘ Or.inr
  mpr := by
    intro hnpnq hpq
    cases hpq
    case inl hp => exact hnpnq.1 hp
    case inr hq => exact hnpnq.2 hq

theorem And.map {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ → p₂) (hq : q₁ → q₂) : p₁ ∧ q₁ → p₂ ∧ q₂
| And.intro hp₁ hq₁ => And.intro (hp hp₁) (hq hq₁)

theorem And.substIff {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ ↔ p₂) (hq : q₁ ↔ q₂) : (p₁ ∧ q₁) ↔ (p₂ ∧ q₂) where
  mp h1 := h1.map hp.mp hq.mp
  mpr h2 := h2.map hp.mpr hq.mpr

theorem Or.map {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ → p₂) (hq : q₁ → q₂) : p₁ ∨ q₁ → p₂ ∨ q₂
| Or.inl hp₁ => Or.inl (hp hp₁)
| Or.inr hq₁ => Or.inr (hq hq₁)

theorem Or.substIff {p₁ p₂ q₁ q₂ : Prop} (hp : p₁ ↔ p₂) (hq : q₁ ↔ q₂) : (p₁ ∨ q₁ ↔  p₂ ∨ q₂) where
  mp h1 := h1.map hp.mp hq.mp
  mpr h2 := h2.map hp.mpr hq.mpr
