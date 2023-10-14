/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Lemmas

/-!
# Auxiliary functions not in the core and `Std`

More auxiliary lemmas are found in `Algdata.Data.Array.Lemmas`.

## TODO

* Give the specification theorem to `Array.anyIdxM` and `Array.anyIdx`.

-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v


namespace Array

variable {α : Type u} {β : Type v}

/-!
### Declaration about `Array.cons`
-/

section Cons

/--
An `Array` counterpart of `List.cons`.

:::note warning
In view of performance, construction based on `Array.push` is preferred.
:::
-/
def cons (a : α) (as : Array α) : Array α :=
  ⟨a :: as.data⟩

@[simp]
theorem data_cons (a : α) (as : Array α) : Array.data (cons a as) = a :: as.data :=
  rfl

@[simp]
theorem size_cons (a : α) (as : Array α) : Array.size (cons a as) = as.size.succ :=
  rfl

theorem push_empty_eq_cons (a : α) : push #[] a = cons a #[] :=
  rfl

theorem push_cons_eq_cons_push (a b : α) (as : Array α) : push (cons a as) b = cons a (push as b) := by
  dsimp [push, cons, List.concat]

@[simp]
theorem getElem_cons_zero {a : α} {x : Array α} : (cons a x)[0]'(x.size.zero_lt_succ) = a :=
  rfl

@[simp]
theorem getElem_cons_succ {a : α} {x : Array α} (i : Nat) (hi : i+1 < x.size+1) : (cons a x)[i+1]'hi = x[i]'(Nat.lt_of_succ_lt_succ hi) :=
  rfl

/-- Induction step for `Array` based on `Array.empty` (aka `#[]`) and `Array.cons`. -/
@[elab_as_elim]
theorem cons_induction
    {motive : Array α → Prop}
    (empty : motive #[])
    (cons : ∀ (a : α) (x : Array α), motive x → motive (cons a x))
    (x : Array α)
  : motive x :=
  x.rec $ List.rec empty λ a as IH => cons a ⟨as⟩ IH

/-- Induction step for `Array` based on `Array.empty` (aka `#[]`) and `Array.cons`. The version takes the major premise as the first argument. -/
@[elab_as_elim]
theorem cons_induction_on
    {motive : Array α → Prop}
    (x : Array α)
    (empty : motive #[])
    (cons : ∀ (a : α) (x : Array α), motive x → motive (cons a x))
  : motive x :=
  x.cons_induction empty cons

/-- Case-splitting for `Array` into `Array.empty` (aka `#[]`) and `Array.cons`. -/
@[elab_as_elim]
theorem cons_cases_on
    {motive : Array α → Prop}
    (x : Array α)
    (empty : motive #[])
    (cons : ∀ (a : α) (x : Array α), motive (cons a x))
  : motive x :=
  x.cons_induction empty fun a x _ => cons a x

end Cons


/-! ### Declarations about `Array.back'` -/

section Back

/-- `back' as h` is the last entry of `as : Array α` with `h : as.size > 0`. In contrast to `Array.back`, this function does not require `Inhabited α` since it doesn't fail thanks to `h`. -/
def back' (as : Array α) (h : as.size > 0) : α :=
  have : as.size - 1 < as.size := Nat.pred_lt' h
  as[as.size - 1]' this

/-- `Array.back'` is a counterpart of `List.getLast`. -/
theorem back'_eq_data_getLast (as : Array α) (h : as.size > 0) : as.back' h = as.data.getLast (h |> as.casesOn λ l (h : l.length > 0) (hc : l = []) => by cases hc; cases h) := by
  rw [List.getLast_eq_get]; rfl

end Back


/-! ### Variants of `Array.any` -/

section Any

variable {m : Type → Type v} [Monad m]

/--
`Array.anyIdxM x p start stop` checks if there is an element in `x : Array α` with indices `start ≤ i < stop` satisfying an index-dependent `Bool`-valued predicate `p : Fin x.size → α → m Bool`.
The last two arguments are optional; the default values are `start := 0` and `stop := x.size`.
This is an index-dependent analogue of `Array.anyM` and a bit less efficient in runtime.
-/
@[inline]
def anyIdxM (x : Array α) (p : Fin x.size → α → m Bool) (start := 0) (stop := x.size) : m Bool :=
  let any (stop : Nat) (h : stop ≤ x.size) :=
    let rec @[specialize] loop (i : Nat) : m Bool := do
      if hlt : i < stop then
        have : i < x.size := trans hlt h
        if (← p ⟨i,this⟩ x[i]) then
          return true
        else
          loop (i+1)
      else
        return false
    loop start
  if h : stop ≤ x.size then
    any stop h
  else
    any x.size .refl
termination_by loop i => stop - i

/--
`Array.anyIdx x p start stop` checks if there is an element in `x : Array α` with indices `start ≤ i < stop` satisfying an index-dependent `Bool`-valued predicate `p : Fin x.size → α → Bool`.
The last two arguments are optional; the default values are `start := 0` and `stop := x.size`.
This is an index-dependent analogue of `Array.any` and a bit less effieicnet in runtime.
If `p` has values in a monad context, use `Array.anyIdxM` instead.
-/
@[inline]
def anyIdx (x : Array α) (p : Fin x.size → α → Bool) (start := 0) (stop := x.size) : Bool :=
  Id.run <| x.anyIdxM p start stop

/-- The runtime implementation of `Array.anyPairM`. -/
@[inline]
unsafe def anyPairMUnsafe (x : Array α) (p : α → α → m Bool) (start := 0) (stop := x.size) : m Bool := do
  let rec @[specialize] any (i j : USize) (stop : USize) : m Bool := do
    if j == stop then
      let i := i + 1
      if i == stop then
        return false
      else
        any i (i+1) stop
    else
      if (← p (x.uget i lcProof) (x.uget j lcProof)) then
        return true
      else
        any i (j+1) stop
  let start := USize.ofNat start
  let stop := USize.ofNat <| min stop x.size
  if start < stop then
    any start (start+1) stop
  else
    return false

/--
`Array.anyPairM x p start stop` check is there is an ordered pair of elements `(x[i],x[j])` in `x : Array α` with indices `start ≤ i < j < stop` satisfying a given `Bool`-valued binary predicate `p : α → α → m Bool` in a monad context.
The last two arguments are optional; the default values are `start := 0` and `stop := x.size`.
-/
@[implemented_by anyPairMUnsafe]
def anyPairM (x : Array α) (p : α → α → m Bool) (start : Nat := 0) (stop : Nat := x.size) : m Bool := do
  let any (stop : Nat) (h : stop ≤ x.size) :=
    let rec loop (i j : Nat) (hij : i < j) : m Bool := do
      if hj : j < stop then
        have : i < x.size := trans (trans hij hj) h
        have : j < x.size := trans hj h
        if (← p x[i] x[j]) then
          return true
        else
          loop i (j+1) (.step hij)
      else
        if i < stop then
          loop (i+1) (i+2) (i+1).lt_succ_self
        else
          return false
    loop start (start+1) start.lt_succ_self
  if h : stop ≤ x.size then
    any stop h
  else
    any x.size .refl
termination_by loop i j _ => (stop - i, stop - j)

/--
`Array.anyPair x p start stop` check is there is an ordered pair of elements `(x[i],x[j])` in `x : Array α` with indices `start ≤ i < j < stop` satisfying a given `Bool`-valued binary predicate `p : α → α → Bool`.
The last two arguments are optional; the default values are `start := 0` and `stop := x.size`.
This function is thought of as the `Bool`-valued `Array`-analogue of `List.Pairwise`.
See also `Array.anyPairM`.
-/
@[inline]
def anyPair (x : Array α) (p : α → α → Bool) (start : Nat := 0) (stop : Nat := x.size) : Bool :=
  Id.run <| x.anyPairM p start stop

theorem anyPairM_loop_empty (p : α → α → m Bool) {stop : Nat} (h : stop ≤ 0) {i j : Nat} (hij : i < j) : anyPairM.loop #[] p stop h i j hij = pure false := by
  cases Nat.eq_zero_of_le_zero h
  unfold anyPairM.loop
  rw [dif_neg j.not_lt_zero, if_neg i.not_lt_zero]

theorem anyPairM_loop_cons_succ (a : α) (x : Array α) (p : α → α → m Bool) {stop : Nat} (h : stop ≤ x.size) {i j : Nat} (hij : i < j)
  : anyPairM.loop (cons a x) p (stop + 1) (Nat.succ_le_succ h) (i+1) (j+1) (Nat.succ_lt_succ hij) = anyPairM.loop x p stop h i j hij := by
  unfold anyPairM.loop
  if hj : j < stop then
    rewrite [dif_pos (Nat.succ_lt_succ hj), dif_pos hj]
    apply bind_congr; intro b
    match b with
    | true => rfl
    | false =>
      simp only [ite_false]
      exact anyPairM_loop_cons_succ a x p h (.step hij)
  else
    rewrite [dif_neg (fun h' => hj (Nat.lt_of_succ_lt_succ h')), dif_neg hj]
    if hi : i < stop then
      rewrite [if_pos (Nat.succ_lt_succ hi), if_pos hi]
      exact anyPairM_loop_cons_succ a x p h (i+1).lt_succ_self
    else
      rw [if_neg (fun h' => hi (Nat.lt_of_succ_lt_succ h')), if_neg hi]
termination_by _ => (stop - i, stop - j)

theorem anyPairM_loop_cons_zero [LawfulMonad m] (a : α) (x : Array α) (p : α → α → m Bool) {stop : Nat} (h : stop ≤ x.size) (j : Nat)
  : anyPairM.loop (cons a x) p (stop + 1) (Nat.succ_le_succ h) 0 (j+1) (j.zero_lt_succ) = x.anyM (p a) j stop >>= fun b => if b then pure true else anyPairM.loop x p stop h 0 1 Nat.zero_lt_one := by
    conv => lhs; unfold anyPairM.loop
    conv => rhs; dsimp [anyM]; rewrite [dif_pos h]; unfold anyM.loop
    simp only [if_pos stop.zero_lt_succ]
    if hj : j < stop then
      simp only [dif_pos (Nat.succ_lt_succ hj), dif_pos hj]
      simp only [getElem_cons_zero, getElem_cons_succ, bind_assoc]
      apply bind_congr; intro b
      match b with
      | true => simp only [ite_true, pure_bind]
      | false =>
        simp only [ite_false]
        rewrite [anyPairM_loop_cons_zero a x p h (j+1)]
        conv => lhs; lhs; dsimp [anyM]; rw [dif_pos h]
    else
      simp only [dif_neg (fun h' => hj (Nat.lt_of_succ_lt_succ h')), dif_neg hj]
      rewrite [anyPairM_loop_cons_succ a x p h Nat.zero_lt_one]
      simp only [pure_bind, ite_false]
termination_by _ => stop - j

@[simp]
theorem anyPairM_empty (p : α → α → m Bool) {start stop : Nat} : anyPairM #[] p start stop = pure false := by
  dsimp [anyPairM]
  simp only [size_toArray, List.length_nil]
  if h : stop ≤ 0 then
    rewrite [dif_pos h]
    exact anyPairM_loop_empty p h start.lt_succ_self
  else
    rewrite [dif_neg h]
    exact anyPairM_loop_empty p .refl start.lt_succ_self

theorem anyPairM_cons_succ (a : α) (x : Array α) (p : α → α → m Bool) {start stop : Nat} : anyPairM (cons a x) p (start + 1) (stop + 1) = anyPairM x p start stop := by
  dsimp [anyPairM]
  if h : stop ≤ x.size then
    rewrite [dif_pos (Nat.succ_le_succ h), dif_pos h]
    exact anyPairM_loop_cons_succ a x p h start.lt_succ_self
  else
    rewrite [dif_neg fun h' => h (Nat.le_of_succ_le_succ h'), dif_neg h]
    exact anyPairM_loop_cons_succ a x p .refl start.lt_succ_self

theorem anyPairM_cons_zero [LawfulMonad m] (a : α) (x : Array α) (p : α → α → m Bool) {stop : Nat} : anyPairM (cons a x) p 0 (stop + 1) = anyM (p a) x 0 stop >>= fun b => if b then return true else anyPairM x p 0 stop := by
  dsimp [anyPairM]
  if h : stop ≤ x.size then
    rewrite [dif_pos (Nat.succ_le_succ h), dif_pos h]
    exact anyPairM_loop_cons_zero a x p h 0
  else
    rewrite [dif_neg fun h' => h (Nat.le_of_succ_le_succ h'), dif_neg h]
    apply Eq.trans <| anyPairM_loop_cons_zero a x p .refl 0
    apply congrFun; apply congrArg
    dsimp [anyM]
    simp only [dif_pos x.size.le_refl, dif_neg h]

theorem anyPairM_cons [LawfulMonad m] (a : α) (x : Array α) (p : α → α → m Bool) : anyPairM (cons a x) p = anyM (p a) x >>= fun b => if b then return true else anyPairM x p :=
  anyPairM_cons_zero a x p

@[simp]
theorem anyPair_empty (p : α → α → Bool) {start stop : Nat} : anyPair #[] p start stop = false :=
  anyPairM_empty (m:=Id) p

theorem anyPair_cons_succ (a : α) (x : Array α) (p : α → α → Bool) {start stop : Nat} : anyPair (cons a x) p (start + 1) (stop + 1) = anyPair x p start stop :=
  anyPairM_cons_succ (m:=Id) a x p

theorem anyPair_cons_zero (a : α) (x : Array α) (p : α → α → Bool) {stop : Nat} : anyPair (cons a x) p 0 (stop + 1) = (any x (p a) 0 stop || anyPair x p 0 stop) := by
  apply Eq.trans <| anyPairM_cons_zero (m:=Id) a x p
  conv =>
    lhs; change if any x (p a) 0 stop = true then true else anyPair x p 0 stop
  match any x (p a) 0 stop with
  | true => simp only [ite_true, Bool.true_or]
  | false => simp only [ite_false, Bool.false_or]

@[simp]
theorem anyPair_cons (a : α) (x : Array α) (p : α → α → Bool) : anyPair (cons a x) p = (any x (p a) || anyPair x p) :=
  anyPair_cons_zero a x p

end Any


/-! ### Declarations about `Array.Nodup` -/

section Nodup

variable [DecidableEq α]

/--
`Array.Nodup x` ensures that `x : Array α` has no duplicate in its elements.
This is an `Array`-counterpart of `List.Nodup`, though it requires `DecidableEq α` in the same spirit of `Membership`.
-/
def Nodup (x : Array α) : Prop :=
  x.anyPair BEq.beq = false

instance Nodup.decidable (x : Array α) : Decidable x.Nodup :=
  inferInstanceAs <| Decidable (x.anyPair BEq.beq = false)

@[simp]
theorem nodup_empty : Nodup (#[] : Array α) := by
  dsimp [Nodup]; exact anyPair_empty BEq.beq

@[simp]
theorem nodup_cons {a : α} {x : Array α} : Nodup (cons a x) ↔ a ∉ x ∧ Nodup x := by
  dsimp [Nodup]
  conv =>
    pattern a ∉ x; change ¬(x.any (BEq.beq a) = true); rw [Bool.not_eq_true]
  rewrite [anyPair_cons_zero]
  match x.any (BEq.beq a) with
  | true => simp only [Bool.true_or, false_and]
  | false => simp only [Bool.false_or, true_and]

end Nodup

end Array
