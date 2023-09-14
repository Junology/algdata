/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Classes.ArrayLike

/-!
# Conainer-types containing subtypes

Given `GetElem V ι α dom`, one can regard `V` as a ***container type*** of elements of type `α` accessed via indices `ι` with domain `dom`.
In this file, we define the type type `ContainerSub V p` for given a (possibly index-depedent) predicate `p : ι → α → Prop` of containers `xs : V` whose elements all satisfy `p`; i.e.
```lean
ContainerSub V p ≡ {x : V // ∀ (i : ι) (_ : dom xs i), p i xs[i]}
```
We show that `ContainerSub V p` admits a sort of interfaces of a container-type (in a bit weaker sense).
In particular, we provide instances for

* `FaithfulGetElem (ContainerSub V p) ι` and
* `SetElem (ContainerSub V p) ι α ContainerSub.DomSet`
* `ArrayLike (ContainerSub V p) ι α dom ContainerSub.DomSet`.

## Main declaration

* `ContainerSub`: the main structure.
* `ContainerSub.DomGet`/`ContainerSub.DomSet`: the side conditions for `GetElem`/`SetElem` instance, if any, respectively.
* `ContainerSub.mapIdx`: mapping a container-type into another using an index-dependent unary operator.
* `ContainerSub.map`: mapping a container into another using an unary operator on elements.
* `ContainerSub.zipWith`

## Implemntation note

We mainly assume that the indexing type `ι` has `DecidableEq`.

-/

-- Disable auto-binding of unbounded variable
set_option autoImplicit false

universe u u₁ u₂ u₃ v w w₁ w₂ w₃


/-! ### Main definition -/

def ContainerSub
    (V : Type u) {ι : Type v} {α : Type w} {dom : V → ι → Prop}
    (p : ι → α → Prop) [GetElem V ι α dom]
  : Type u :=
  {xs : V // ∀ (i : ι) (hi : dom xs i), p i (xs[i]'hi)}


namespace ContainerSub

/-! ### Basic declarations -/

section Basic

variable {V : Type u} {ι : Type v} {α : Type w}
variable {dom : V → ι → Prop} {domSet : V → ι → α → Prop}
variable {p : ι → α → Prop}

section 

variable [GetElem V ι α dom]

/-- Two elements `xs ys : ContainerSub V p` equal to each other if their underlying structures do. -/
@[ext]
theorem eq {xs ys : ContainerSub V p} : xs.val = ys.val → xs = ys :=
  Subtype.eq

/-- The side condition for `GetElem` instance. -/
abbrev DomGet (xs : ContainerSub V p) (i : ι) : Prop :=
  dom xs.val i

instance instGetElem : GetElem (ContainerSub V p) ι α DomGet where
  getElem xs := getElem xs.val

instance instFaithfulGetElem [FaithfulGetElem V ι] : FaithfulGetElem (ContainerSub V p) ι where
  ext xs ys hdom hget :=
    eq <| FaithfulGetElem.ext xs.val ys.val hdom hget

/-- Get the `i`-th element in `xs : ArraySub V ι p` together with the proof that it satisfies `p i`. -/
@[inline]
def get' (xs : ContainerSub V p) (i : ι) (hi : DomGet xs i) : Subtype (p i) :=
  .mk (xs.val[i]'hi) <| xs.property i hi

@[simp]
theorem val_get' (xs : ContainerSub V p) {i : ι} {hi : DomGet xs i}
  : (xs.get' i hi).val = xs[i]'hi :=
  rfl

end


section

variable [ArrayLike V ι α dom domSet] [DecidableEq ι]

/-- The side condition for `SetElem` instance. -/
abbrev DomSet [SetElem V ι α domSet] (xs : ContainerSub V p) (i : ι) (a : α) : Prop :=
  domSet xs.val i a ∧ p i a  

instance instArrayLike : ArrayLike (ContainerSub V p) ι α DomGet DomSet where
  setElem xs i a hi :=
    .mk (xs.val{i ≔ a ∵ hi.1}) fun j hj => by
      if h : i = j then
        cases h; rw [ArrayLike.get_set_eq (cont:=V) (h:=hi.1)]; exact hi.2
      else
        rw [ArrayLike.get_set_ne xs.val h]
        exact xs.property j (ArrayLike.set_noexpand (xs:=xs.val) hj)
  dom_set {xs i a} hi := ArrayLike.dom_set (xs:=xs.val) hi.1
  set_noexpand {xs i a hi j} := ArrayLike.set_noexpand (xs:=xs.val)
  get_set_eq xs i a := ArrayLike.get_set_eq xs.val i a
  get_set_ne xs i j hij a hi hj := ArrayLike.get_set_ne xs.val hij a hj
  modify xs i hi f hf :=
    .mk (ArrayLike.modify xs.val i hi f hf.1) fun j hj => by
      simp [ArrayLike.modify_eq] at hj ⊢
      if h : i = j then
        cases h; simp only [ArrayLike.get_set_eq]; exact hf.2
      else
        rw [ArrayLike.get_set_ne xs.val h _ hj]
        exact xs.property j <| ArrayLike.set_noexpand (xs:=xs.val) hj
  modify_eq {xs i hi f hf} :=
    Subtype.eq $ ArrayLike.modify_eq (xs:=xs.val)

#print axioms instArrayLike

end

end Basic


/-! ### Declaration about `ArraySub.mapIdx`/`ArraySub.map` -/

section Map

variable {V : Type u} {W : Type u₁} {ι : Type v} {α : Type w} {β : Type w₁}
variable {domGet : V → ι → Prop} {domSet : V → ι → α → Prop}
variable {domGet' : W → ι → Prop} {domSet' : W → ι → β → Prop}
variable [DecidableEq ι]
variable [ArrayLike V ι α domGet domSet] [ArrayLike W ι β domGet' domSet']
variable [MapIdxElem V W ι]
variable {p : ι → α → Prop} {q : ι → β → Prop}

/-- `ArraySub.mapIdx xs f hf` maps an array-like structure `xs` of subtypes into another with an index-dependent unary operation `f` and proof of consistency `hf`; for index-independent version, see `ArraySub.map` with attention to the order of the arguments. -/
@[inline]
def mapIdx (xs : ContainerSub V p) (f : (i : ι) → DomGet xs i → α → β) (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f i hi (xs[i]'hi))) : ContainerSub W q :=
  .mk (MapIdxElem.mapIdxElem xs.val f) fun i hi => by
    rw [MapIdxElem.get_mapIdxElem xs.val f i hi]
    exact hf i <| MapIdxElem.noexpand xs.val f i hi

theorem mapIdx_noexpand
    (xs : ContainerSub V p) (f : (i : ι) → DomGet xs i → α → β)
    (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f i hi (xs[i]'hi)))
    {i : ι}
    (h : DomGet (mapIdx xs f hf : ContainerSub W q) i)
  : DomGet xs i :=
  MapIdxElem.noexpand xs.val f i h

@[simp]
theorem get_mapIdx
    (xs : ContainerSub V p) (f : (i : ι) → DomGet xs i → α → β)
    (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f i hi (xs[i]'hi)))
    (i : ι) {hi : DomGet (mapIdx xs f hf) i}
  : (mapIdx xs f hf : ContainerSub W q)[i]'hi = f i (mapIdx_noexpand xs f hf hi) (xs[i]'(mapIdx_noexpand xs f hf hi)) :=
  MapIdxElem.get_mapIdxElem xs.val f i hi

/--
`ArraySub.map f xs hf` maps an array-like structure `xs` of subtypes into another with an index-independent unary operator `f` and proof of consistency `hf`; for index-dependent version, see `ArraySub.mapIdx` with attention to the order of the arguments.

:::note info
The function no longer takes the indexing type `ι` as an explicit argument in contrast to `MapIdxElem.map`.
This is because the argument type `ContainerSub V p` can determine it.
:::
-/
@[inline]
def map (f : α → β) (xs : ContainerSub V p) (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f (xs[i]'hi))) : ContainerSub W q :=
  .mk (MapIdxElem.map ι f xs.val) fun i hi =>
    MapIdxElem.get_map f xs.val i hi ▸
      hf i (MapIdxElem.noexpand xs.val (fun _ _ => f) i hi)

theorem map_noexpand
    (f : α → β) (xs : ContainerSub V p)
    (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f (xs[i]'hi)))
    (i : ι) (hi : DomGet (map f xs hf : ContainerSub W q) i)
  : DomGet xs i :=
  MapIdxElem.map_noexpand (idx:=ι) f xs.val i hi

theorem get_map
    (f : α → β) (xs : ContainerSub V p)
    (hf : ∀ (i : ι) (hi : DomGet xs i), q i (f (xs[i]'hi)))
    (i : ι) (hi : DomGet (map f xs hf : ContainerSub W q) i)
  : (map f xs hf)[i]'hi = f (xs[i]'(map_noexpand f xs hf i hi)) :=
  MapIdxElem.get_map f xs.val i hi

#print axioms get_map

end Map


/-! ### Declaration about `ContainerSub.zipWith` -/

section ZipWith

variable {U : Type u₁} {V : Type u₂} {W : Type u} {ι : Type v}
variable {α : Type w₁} {β : Type w₂} {γ : Type w}
variable {domU : U → ι → Prop} {domU' : U → ι → α → Prop} {domV : V → ι → Prop}
variable {domW : W → ι → Prop} {domW' : W → ι → γ → Prop}
variable [DecidableEq ι]
variable [ArrayLike U ι α domU domU'] [ArrayLike W ι γ domW domW']
variable [MapIdxElem U W ι] [GetElem V ι β domV]
variable {p : ι → α → Prop} {q : ι → β → Prop} {r : ι → γ → Prop}

/--
`ContainerSub.zipWith f xs ys hdom hf` zips `xs : ContainerSub U p` and `ys : ContainerSub V q` together into the type `ContainerSub W r` with a binary operator `f : α → β → γ` provided the proofs
* `hdom`: that the valid indices of `xs` are also valid for `ys`;
* `hf`: the result of the binary operator `f` satisfies the predicate `r` of the resulting type.
:::note info
The argument order follows `Array.zipWith` rather than `List.zipWith`.
:::
-/
@[inline]
def zipWith
    (xs : ContainerSub U p) (ys : ContainerSub V q)
    (hdom : ∀ (i : ι), DomGet xs i → DomGet ys i)
    (f : α → β → γ)
    (hf : ∀ (i : ι) (hxi : DomGet xs i) (hyi : DomGet ys i), r i (f xs[i] ys[i]))
  : ContainerSub W r :=
  .mk (MapIdxElem.zipWith xs.val ys.val hdom f) fun j hj =>
    MapIdxElem.get_zipWith xs.val ys.val hdom f j hj ▸
      hf j
        (MapIdxElem.zipWith_noexpand_left (xs:=xs.val) hj)
        (MapIdxElem.zipWith_noexpand_right (xs:=xs.val) hj)

theorem zipWith_noexpand_left
    (xs : ContainerSub U p) (ys : ContainerSub V q)
    (hdom : ∀ (i : ι), DomGet xs i → DomGet ys i)
    (f : α → β → γ)
    (hf : ∀ (i : ι) (hxi : DomGet xs i) (hyi : DomGet ys i), r i (f xs[i] ys[i]))
    (i : ι) (hi : DomGet (zipWith xs ys hdom f hf : ContainerSub W r) i)
  : DomGet xs i :=
  MapIdxElem.zipWith_noexpand_left (xs:=xs.val) hi

theorem zipWith_noexpand_right
    (xs : ContainerSub U p) (ys : ContainerSub V q)
    (hdom : ∀ (i : ι), DomGet xs i → DomGet ys i)
    (f : α → β → γ)
    (hf : ∀ (i : ι) (hxi : DomGet xs i) (hyi : DomGet ys i), r i (f xs[i] ys[i]))
    (i : ι) (hi : DomGet (zipWith xs ys hdom f hf : ContainerSub W r) i)
  : DomGet ys i :=
  MapIdxElem.zipWith_noexpand_right hi

theorem get_zipWith
    (xs : ContainerSub U p) (ys : ContainerSub V q)
    (hdom : ∀ (i : ι), DomGet xs i → DomGet ys i)
    (f : α → β → γ)
    (hf : ∀ (i : ι) (hxi : DomGet xs i) (hyi : DomGet ys i), r i (f xs[i] ys[i]))
    (i : ι) (hi : DomGet (zipWith xs ys hdom f hf : ContainerSub W r) i)
  : (zipWith xs ys hdom f hf)[i]'hi = f (xs[i]'(zipWith_noexpand_left xs ys hdom f hf i hi)) (ys[i]'(zipWith_noexpand_right xs ys hdom f hf i hi)) :=
  MapIdxElem.get_zipWith xs.val ys.val hdom f i hi

#print axioms get_zipWith

end ZipWith

end ContainerSub

