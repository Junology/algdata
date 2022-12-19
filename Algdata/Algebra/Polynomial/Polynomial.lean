/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Data.KVChain.Basic
import Algdata.Data.KVChain.MergeWith
import Algdata.Algebra.Monoid.FreeCMonoid
import Algdata.Algebra.Polynomial.MonomialOrder

/-!
# Polynomial on linearly ordered variables.
-/

universe u v

@[inline]
protected
abbrev Polynomial.Coeff (ρ : Type u) [OfNat ρ (nat_lit 0)] := {x : ρ // x ≠ (0 : ρ)}

@[inline]
protected
abbrev Polynomial.binop {ρ : Type u} [OfNat ρ (nat_lit 0)] [DecidableEq ρ] (f : ρ → ρ → ρ) : Polynomial.Coeff ρ → Polynomial.Coeff ρ → Option (Polynomial.Coeff ρ) :=
  λ x y =>
    let z := f x.val y.val
    if h : z = 0 then none else some ⟨z,h⟩

structure Polynomial (ρ : Type u) (α : Type v) [OfNat ρ (nat_lit 0)] [DecidableEq α] [LinearLT α] [DecidableRel (α:=α) LT.lt] (o : MonomialOrder α) where
  terms : KVChain o.gt (λ _ : FreeCMonoid α => Polynomial.Coeff ρ)


namespace Polynomial

/-!
## Instances
-/

section Instances

variable {ρ : Type u} {α : Type v} [DecidableEq α] [LinearLT α] [DecidableRel (α:=α) LT.lt] {o : MonomialOrder α}

-- Notation to construct monomials
-- cf. in `Prelude`:
--   infixl:65 " + "   => HAdd.hAdd
--   infixl:70 " * "   => HMul.hMul
--   infixr:80 " ^ "   => HPow.hPow

protected
def reprPrec [OfNat ρ (nat_lit 0)] [Repr ρ] [Repr α] (f : Polynomial ρ α o) (prec : Nat) : Lean.Format :=
  let g : Sigma (λ _ : FreeCMonoid α => Polynomial.Coeff ρ) → Std.Format :=
    λ t => match t.1.vars.toList with
      | [] => repr t.2
      | (_::_) => reprPrec t.2 70 ++ "⊙" ++ reprPrec t.1 70
  match f.terms.toList with
  | [] => "0"
  | [t] => ite (prec > 70) Std.Format.paren id $ g t
  | (t::ts) =>
    ite (prec > 65) Std.Format.paren id $ ts.foldl (λ s t => s ++ " + " ++ g t) (g t)

def reprPrettyPrec [OfNat ρ (nat_lit 0)] [Repr ρ] [Repr α] (f : Polynomial ρ α o) (prec : Nat) : Lean.Format :=
  let g : Sigma (λ _ : FreeCMonoid α => Polynomial.Coeff ρ) → Std.Format :=
    λ t => match t.1.vars.toList with
      | [] => repr t.2
      | (_::_) => reprPrec t.2 70 ++ "⊙" ++ FreeCMonoid.reprPrettyPrec t.1 70
  match f.terms.toList with
  | [] => "0"
  | [t] => ite (prec > 70) Std.Format.paren id $ g t
  | (t::ts) =>
    ite (prec > 65) Std.Format.paren id $ ts.foldl (λ s t => s ++ " + " ++ g t) (g t)

def reprPretty [OfNat ρ (nat_lit 0)] [Repr ρ] [Repr α] : Polynomial ρ α o → Lean.Format :=
  λ f => reprPrettyPrec f 0

def pretty [OfNat ρ (nat_lit 0)] [Repr ρ] [Repr α] : Polynomial ρ α o → String :=
  λ f => (reprPretty f).pretty

instance instReplPolynomial [OfNat ρ (nat_lit 0)] [Repr ρ] [Repr α] : Repr (Polynomial ρ α o) where
  reprPrec x prec := Polynomial.reprPrec x prec

instance polynomialHasDecidableEq [DecidableEq ρ] [OfNat ρ (nat_lit 0)] : DecidableEq (Polynomial ρ α o)
| Polynomial.mk xdata, Polynomial.mk ydata =>
  if h : xdata = ydata then
    isTrue $ h ▸ rfl
  else
    isFalse $ h ∘ congrArg Polynomial.terms

instance instAddPolynomial [DecidableEq ρ] [Add ρ] [OfNat ρ (nat_lit 0)] : Add (Polynomial ρ α o) where
  add x y := {terms := x.terms.mergeWith (λ _ => Polynomial.binop (ρ:=ρ) Add.add) y.terms}

instance instSubPolynomial [DecidableEq ρ] [Sub ρ] [OfNat ρ (nat_lit 0)] : Sub (Polynomial ρ α o) where
  sub x y := {terms := x.terms.mergeWith (λ _ => Polynomial.binop (ρ:=ρ) Sub.sub) y.terms}

instance instOfNatZeroPolynomial [OfNat ρ (nat_lit 0)] : OfNat (Polynomial ρ α o) (nat_lit 0) where
  ofNat := Polynomial.mk KVChain.nil

instance instOfNatOnePolynomial [DecidableEq ρ] [OfNat ρ (nat_lit 0)] [OfNat ρ (nat_lit 1)] : OfNat (Polynomial ρ α o) (nat_lit 1) where
  ofNat :=
    let x : ρ := 1
    if h : x = 0 then ⟨KVChain.nil⟩ else {terms := KVChain.singleton 1 ⟨x,h⟩}

instance instOfNatPolynomial [DecidableEq ρ] [OfNat ρ (nat_lit 0)] {n : Nat} [OfNat ρ n] : OfNat (Polynomial ρ α o) n where
  ofNat :=
    let x := OfNat.ofNat (α:=ρ) n
    if h : x = 0 then ⟨KVChain.nil⟩ else {terms := KVChain.singleton 1 ⟨x,h⟩}

instance instMulPolynomial [DecidableEq ρ] [Add ρ] [Mul ρ] [OfNat ρ (nat_lit 0)] : Mul (Polynomial ρ α o) where
  mul x y :=
    let f : Polynomial ρ α o → Sigma (λ _ : FreeCMonoid α => Polynomial.Coeff ρ) → Polynomial ρ α o :=
      have : Trans (λ x y=>o.lt y x) (λ x y=>o.lt y x) (λ x y=>o.lt y x) := inferInstanceAs (Trans o.gt o.gt o.gt)
      λ g t => g + Polynomial.mk (o:=o) (x.terms.filterMapKV (r₁:=o.gt) (β₁:=λ _ : FreeCMonoid α=> Polynomial.Coeff.{u} ρ) (λ a => Mul.mul a t.1) (λ _ b => Polynomial.binop Mul.mul b t.2) (λ _ _ => o.mul_lt_mul_right _ _ _))
    List.foldl f (0 : Polynomial ρ α o) y.terms

end Instances


/-!
## Constructions
-/

variable {ρ : Type u} {α : Type v} [DecidableEq ρ] [DecidableEq α] [LinearLT α] [DecidableRel (α:=α) LT.lt] [OfNat ρ (nat_lit 0)]

--- Monomial together with a coefficient as a polynomial
def monomial (r : ρ) (x : List (α × Nat)) (o : MonomialOrder α := MonomialOrder.deglex) : Polynomial ρ α o where
  terms :=
    if h : r = 0 then
      KVChain.nil
    else
       KVChain.singleton (β:=λ _ : FreeCMonoid α => Polynomial.Coeff ρ) (FreeCMonoid.fromList x) ⟨r,h⟩

infixl:70 " ⊙ " => Polynomial.monomial

--- Define a ring homomorphism out of polynomials in terms of the images of variables.
def elim {β : Type _} [OfNat β (nat_lit 0)] [OfNat β (nat_lit 1)] [HAdd β β β] [HMul β β β] [HPow β Nat β] {o : MonomialOrder α} (coeff : ρ → β) (var : α → β) (f : Polynomial ρ α o) : β :=
  f.terms.foldl (λ b xs r => b + coeff r.1 * xs.elim var) 0

end Polynomial

