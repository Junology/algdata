/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas

import Algdata.Data.Array.Lemmas
import Algdata.Data.Array.Sized

/-!
# Array-like interface class

In this file, we define several classes for array-like read/write access interface on structures.
In particular, structures with *fixed sizes* get special treatments.
The main target structures include `List`, `Array`, and `SizedArray`.

## Main declaration

* `SetElem` is a "write"-counterpart of `GetElem` in the core and implements the notation `arr{i ≔ a}` which is supposed to represent the term obtained by substituting `a` into the `i`-th position in the array-like structure `arr`.
* `FaithfulGetElem` ensures that, for a given instance `GetElem cont idx elem dom`, two terms `x y : cont` of a container type equal to each other as soon as the side conditions `dom x i` and `dom y i` are equivalent and `x[i] = y[i]` for every valid index `i`.
* `ArrayLike` extends both `GetElem` and `SetElem` and ensures consistency of get-set operations;
* `SizedArrayLike` is similar to `ArrayLike` while the index bound is fixed.

-/

-- Disable auto-binding of unbounded variable
set_option autoImplicit false

universe u v w


/-! ### SetElem -/

/--
The class `SetElem cont idx elem dom` is a "Write"-counterpart of `GetElem cont idx elem dom` saying "one can substitute an element `e : elem` into the position `i : idx` of the container `xs : cont` provided the condition `dom xs i` is satisfied".
As in the case of `GetElem`, the class implements `xs{i ≔ e}` notation.

When one uses this notation, the proof side-condition `dom xs i` is automatically dispatched by the `get_elem_tactic` tactic, which can be extended by adding more clauses to `get_elem_tactic_trivial`.
-/
class SetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → elem → Prop)) where
  /--
  The syntax `arr{i ≔ a}` represents the new term obtained by substituting `a : elem` into the position `i : idx` in the container `arr : cont` (e.g. `cont ≡ Array α`).
  If there are proof side conditions to the application, they will be automatically inferred by the `get_elem_tactic` tactic.

  The actual behavior of this class is type-dependent, but here are some important implementations:
  * `arr{i ≔ a} : Array α` where `arr : Array α`, `a : α`, and `i : Nat` or `i : USize`:
    does array indexing with no bounds check and a proof side goal `i < arr.size`.
  * `l{i ≔ a} : List α` where `l : List α`, `a : α`, and `i : Nat`: index into a list,
    with proof side goal `i < l.length`.

  There are other variations on this syntax:
  * `arr{i ≔ a}`: proves the proof side goal by `get_elem_tactic`
  * `arr{i !≔ a}`: panics if the side goal is false
  * `arr{i ∵ h ≔ a}`: uses `h` to prove the side goal
  - `set arr i a h`
  -/
  setElem (xs : cont) (i : idx) (e : elem) : dom xs i e → cont

namespace SetElem

variable {cont : Type u} {idx : Type v} {elem : Type w} {dom : cont → idx → elem → Prop}
variable [SetElem cont idx elem dom]

/-- `SetElem.setElem! xs i e` substitutes `e` into the `i`-th position in `xs` without any proof; it panics if the side goal is false. -/
def setElem! (xs : cont) (i : idx) (e : elem) [Decidable (dom xs i e)] := 
  if h : dom xs i e then
    setElem xs i e h
  else
    @panic cont ⟨xs⟩ "index out of bounds"

declare_syntax_cat set_elem_setter

syntax:min term " ≔ " term : set_elem_setter
syntax:min term " !≔ " term : set_elem_setter
syntax:min term " ≔ " term " ∵ " term : set_elem_setter

@[inherit_doc SetElem.setElem]
syntax:max (name := setElemMacro) term noWs "{" withoutPosition(set_elem_setter,*) "}" : term

open Lean in
@[macro setElemMacro] def setElemImpl : Macro
| `(term| $xs{}) => `($xs)
| `(term| $xs{$setters:set_elem_setter,*}) => do
  let mut xs := xs
  for s in setters.getElems do
    match s with
    | `(set_elem_setter| $i:term ≔ $a:term) =>
      xs ← `(SetElem.setElem $xs $i $a (by get_elem_tactic))
    | `(set_elem_setter| $i:term !≔ $a:term) =>
      xs ← `(SetElem.setElem! $xs $i $a)
    | `(set_elem_setter| $i:term ≔ $a:term ∵ $h:term) =>
      xs ← `(SetElem.setElem $xs $i $a $h)
    | _ => Macro.throwUnsupported
  return xs
| _ => Macro.throwUnsupported

end SetElem

instance (α : Type u) : SetElem (Array α) Nat α fun x i _ => i < x.size where
  setElem arr i a h := arr.set ⟨i,h⟩ a

@[simp]
theorem Array.size_setElem {α : Type u} (arr : Array α) (i : Nat) (a : α) {hi : i < arr.size} : Array.size arr{i ≔ a ∵ hi} = arr.size :=
  arr.size_set ⟨i,hi⟩ a

instance (α : Type u) : SetElem (List α) Nat α fun x i _ => i < x.length where
  setElem l i a _ := l.set i a

@[simp]
theorem List.length_setElem {α : Type u} (l : List α) (i : Nat) (a : α) {hi : i < l.length} : List.length l{i ≔ a ∵ hi} = l.length :=
  l.length_set i a


/-! ### Faithful GetElem -/

section FaithfulGetElem

/--
Given an instance `GetElem cont idx elem dom`, `FaithfulGetElem cont idx elem dom` ensures that two containers `x y : cont` equal to each other as soon as
* the side conditions are equivalent; i.e. `∀ i, dom x i ↔ dom y i`;
* their contents all agree; i.e. `∀ i, x[i] = y[i]`.
-/
class FaithfulGetElem (cont : Type u) (idx : Type v) {elem : outParam (Type w)} {dom : outParam (cont → idx → Prop)} [GetElem cont idx elem dom] : Prop where
  ext (x y : cont) : (∀ (i : idx), dom x i ↔ dom y i) → (∀ (i : idx) (hx : dom x i) (hy : dom y i), x[i]'hx = y[i]'hy) → x = y

private theorem _root_.Nat.le_of_lt_imp_lt {m n : Nat} (h : ∀ k : Nat, k < m → k < n) : m ≤ n :=
  match m with
  | 0 => n.zero_le
  | m+1 => h m m.lt_succ_self

private theorem _root_.Nat.eq_of_lt_iff_lt {m n : Nat} (h : ∀ k : Nat, k < m ↔ k < n) : m = n :=
  Nat.le_antisymm
    (Nat.le_of_lt_imp_lt fun i => (h i).mp)
    (Nat.le_of_lt_imp_lt fun i => (h i).mpr)

instance (α : Type u) : FaithfulGetElem (Array α) Nat where
  ext x y hsize h :=
    Array.ext x y (Nat.eq_of_lt_iff_lt hsize) h

instance (α : Type u) : FaithfulGetElem (List α) Nat where
  ext _ _ hlength h :=
    List.ext_get (Nat.eq_of_lt_iff_lt hlength) h

instance (α : Type u) (n : Nat) : FaithfulGetElem (SizedArray α n) Nat where
  ext x y _ h := SizedArray.ext x y fun i hi => h i hi hi

instance (α : Type u) (n m : Nat) (h : n ≤ m := by get_elem_tactic) : @FaithfulGetElem (SizedArray α n) (Fin m) _ _ instGetElemFinVal where
  ext x y _ hxy :=
    FaithfulGetElem.ext x y
      (fun i : Nat => Iff.refl (i < n))
      (fun i hi _ => hxy ⟨i,trans hi h⟩ hi hi)

end FaithfulGetElem


/-! ### Array-like structures -/

/-- `Array cont idx elem domGet domSet ` asserts that `cont` is an array-like type with indices of type `idx` and elements of type `elem` with read/write index validators being `domGet` and `domSet` respectively. Major instances include `List` and `Array`. -/
class ArrayLike (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (domGet : outParam (cont → idx → Prop)) (domSet : outParam (cont → idx → elem → Prop)) extends GetElem cont idx elem domGet, SetElem cont idx elem domSet where
  dom_imp {xs: cont} {i : idx} : ∀ {e : elem}, domSet xs i e → domGet xs i :=
    by intros; trivial
  /-- `ArrayLike.noshrink` guarantees that `j : idx` is a valid index for `xs{i ≔ e}` as soon as it is for `xs`.-/
  noshrink {xs : cont} {i : idx} {e : elem} {h : domSet xs i e} {j : idx} : domGet xs j → domGet xs{i ≔ e ∵ h} j
  /-- cf `List.get_set_eq` and `Array.get_set_eq`. -/
  get_set_eq (xs : cont) (i : idx) (e : elem) {h : domSet xs i e} : xs{i ≔ e ∵ h}[i]'(noshrink <| dom_imp h) = e
  /-- cf `List.get_set_ne` and `Array.get_set_ne`. -/
  get_set_ne (xs : cont) {i j : idx} (h : i ≠ j) (e : elem) {hi : domSet xs i e} (hj : domGet xs j) : xs{i ≔ e ∵ hi}[j]'(noshrink hj) = xs[j]'(hj)

instance (α : Type u) : ArrayLike (Array α) Nat α (fun as i => i < as.size) (fun as i _ => i < as.size) where
  noshrink {as i a h _} hj := trans (s:=Eq) hj (as.size_set ⟨i,h⟩ a).symm
  get_set_eq as i a {h} := as.get_set_eq ⟨i,h⟩ a
  get_set_ne as i _ h a hi hj := as.get_set_ne ⟨i,hi⟩ a hj h

instance (α : Type u) : ArrayLike (List α) Nat α (fun l i => i < l.length) (fun l i _ => i < l.length) where
  noshrink {l i a _ _} hj := trans (s:=Eq) hj (l.length_set i a).symm
  get_set_eq l i a {h} := l.get_set_eq i a (l.length_set i a ▸ h)
  get_set_ne l i _ h a _ hj := l.get_set_ne h a (l.length_set i a ▸ hj)

namespace ArrayLike

variable {cont : Type u} {idx : Type v} {elem : Type w} {domGet : cont → idx → Prop} {domSet : cont → idx → elem → Prop}
variable [ArrayLike cont idx elem domGet domSet]

theorem get_set_ite [DecidableEq idx] (xs : cont) (i j : idx) (e : elem) {hi : domSet xs i e} {hj : domGet xs j} : xs{i ≔ e ∵ hi}[j]'(noshrink hj) = if i = j then e else xs[j]'hj := by
  if h : i = j then
    cases h
    exact Eq.trans (get_set_eq xs i e) (if_pos rfl).symm
  else
    exact Eq.trans (get_set_ne xs h e hj) (if_neg h).symm

end ArrayLike


/-! ### Array-like structure with fixed size -/

/--
`SizedArrayLike cont idx elem domGet domSet` asserts that `cont` is an array-like structure type with the side conditions `domGet`/`domSet` independent of arrays.
For example, the fixed length array `SizedArray α n` has the instance for
```lean
SizedArrayLike (SizedArray α n) Nat α (· < n) (fun i _ => i < n)
```
It is implemented as a special case of `ArrayLike` as
```lean
ArrayLike cont idx elem (fun i _ => domGet i) (fun i _ e => domSet i e)
```
Thanks to the independency, the `ArrayLike.noshrink` field is filled automatically.
-/
class SizedArrayLike (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (domGet : outParam (idx → Prop)) (domSet : outParam (idx → elem → Prop)) extends ArrayLike cont idx elem (fun _ => domGet) (fun _ => domSet) where
  noshrink := id

instance (α : Type u) (n : Nat) : SizedArrayLike (SizedArray α n) Nat α (· < n) (fun i _ => i < n) where
  setElem arr i a h := arr.set ⟨i,h⟩ a
  get_set_eq arr i a h := arr.get_set_eq ⟨i,h⟩ a
  get_set_ne arr i _ h a hi hj := arr.get_set_ne ⟨i,hi⟩ a hj h


namespace SizedArrayLike

variable {cont : Type u}

section Basic

variable {idx : Type v} {elem : Type w} {domGet : idx → Prop} {domSet : idx → elem → Prop}
variable [SizedArrayLike cont idx elem domGet domSet]

theorem ext [FaithfulGetElem cont idx] (xs ys : cont) (h : ∀ (i : idx) (hi : domGet i), xs[i]'hi = ys[i]'hi) : xs = ys :=
  FaithfulGetElem.ext (idx:=idx) xs ys
    (fun i => Iff.refl (domGet i))
    (fun i hx _ => h i hx)

end Basic


section OfFn

variable {elem : Type w} {len : Nat}
variable [SizedArrayLike cont Nat elem (· < len) (fun i _ => i < len)]

variable (cont) in
/--
Construct an array-like structure from a function out of `Fin dim`.
In particular, we have the following (see `get_ofFn`):
```lean
∀ (i : Fin dim), (ofFn f)[i] = f i
```
-/
def ofFn [Inhabited cont] (f : Fin len → elem) : cont := go 0 default where
  go (i : Nat) (x : cont) : cont :=
    if h : i < len then go (i+1) x{i ≔ f ⟨i,h⟩ ∵ h} else x
  termination_by _ => len - i

theorem get_ofFn_go (f : Fin len → elem) (i j : Nat) (hi : i < len) (x : cont) : (i ≥ j → (ofFn.go cont f j x)[i]'hi = f ⟨i,hi⟩) ∧ (i < j → (ofFn.go cont f j x)[i]'hi = x[i]'hi) := by
  unfold ofFn.go
  if hj : j < len then
    simp only [dif_pos hj]
    have IH := get_ofFn_go f i (j+1) hi
    apply And.intro
    . show i ≥ j → _
      intro hij
      cases Nat.eq_or_lt_of_le hij with
      | inl heq =>
        cases heq
        apply Eq.trans ((IH _).2 i.lt_succ_self)
        exact ArrayLike.get_set_eq x i (f ⟨i,hi⟩)
      | inr hgt => exact Eq.trans ((IH _).1 hgt) rfl
    . show i < j → _
      intro hij
      apply Eq.trans ((IH _).2 (Nat.lt_succ_of_lt hij))
      exact ArrayLike.get_set_ne x (Nat.ne_of_gt hij) (f ⟨j,hj⟩) hi
  else
    simp only [dif_neg hj]
    refine And.intro ?_ (fun _ => True.intro)
    intro hij
    have : len ≤ i := trans (r:=LE.le) (s:=LE.le) (Nat.ge_of_not_lt hj) hij
    exact False.elim <| Nat.le_lt_antisymm this hi
termination_by _ => len - j

theorem get_ofFn [Inhabited cont] (f : Fin len → elem) (i : Nat) {hi : i < len} : (ofFn cont f)[i]'hi = f ⟨i,hi⟩ :=
  (get_ofFn_go f i 0 hi (default : cont)).1 i.zero_le

end OfFn

end SizedArrayLike
