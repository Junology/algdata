/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Lemmas

import Dijkstra.Control.Functor.Subreg
import Algdata.Data.Array.Lemmas

/-!
# Fixed-sized array
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u u₁ u₂ v v₁ v₂ w uu

/-- Fixed-sized array -/
@[unbox]
structure SizedArray (α : Type u) (n : Nat) where
  val : Array α
  size_eq : val.size = n
deriving DecidableEq, Repr

namespace SizedArray


/-! ## Basic declaration -/

section Basic

variable {α : Type u} {β : Type v} {n : Nat}

/-- Construct an empty array. -/
@[match_pattern]
abbrev empty : SizedArray α 0 :=
  ⟨Array.empty, rfl⟩

/-- The same as `SizedArray.empty` while this version uses `Array.mkEmpty` to construct the underlying (empty) array. -/
abbrev mkEmpty (n : Nat) : SizedArray α 0 :=
  ⟨Array.mkEmpty n, rfl⟩

def subst {m : Nat} (h : n = m) (x : SizedArray α n) : SizedArray α m :=
  ⟨x.val, x.size_eq.trans h⟩

def _root_.Array.toSized (x : Array α) : SizedArray α x.size :=
  ⟨x,rfl⟩

/-- `SizedArray.val : SizedArray α n → Array α` is injective; in other words, every sized array `x : SizedArray α n` is determined by its value on `x.val`. -/
theorem val_inj : ∀ {x y : SizedArray α n}, x.val = y.val → x = y
| mk _ _, mk _ _, rfl => rfl

theorem eq_of_data_eq : ∀ {x y : SizedArray α n}, x.val.data = y.val.data → x = y
| mk (.mk _) _, mk (.mk _) _, rfl => rfl

theorem eq_empty (x : SizedArray α 0) : x = empty :=
  match x with | mk (.mk []) _ => rfl

instance getElem : GetElem (SizedArray α n) Nat α (λ _ i => i < n) where
  getElem x i h := x.val[i]'(x.size_eq.symm ▸ h)

/-- Two `SizedArray α n` equal to each other as soon as their contents all coincide. -/
@[ext]
theorem ext (x y : SizedArray α n) (h : ∀ (i : Nat), (hi : i < n) → x[i] = y[i]) : x = y :=
  val_inj $ Array.ext x.val y.val (x.size_eq.trans y.size_eq.symm) λ i hi₁ hi₂ =>
    calc x.val[i]
        = x[i]'(x.size_eq.symm ▸ hi₁) := rfl
      _ = y[i]'(y.size_eq.symm ▸ hi₂) := h i _
      _ = y.val[i] := rfl

/-- Insert an element to the head of an array. -/
def cons (a : α) (x : SizedArray α n) : SizedArray α (n+1) :=
  ⟨⟨a::x.val.data⟩, congrArg Nat.succ x.size_eq⟩

/-- Get the first element of an array. -/
def head (x : SizedArray α (n+1)) : α :=
  x[0]'(n.zero_lt_succ)

/-- Remove the first element. -/
def tail (x : SizedArray α (n+1)) : SizedArray α n :=
  mk ⟨x.val.data.tail⟩ $ by
    dsimp [Array.size]
    rw [List.length_tail]
    exact congrArg (·-1) x.size_eq

theorem cons_head_tail (x : SizedArray α (n+1)) : .cons x.head x.tail = x :=
  match x with
  | mk (.mk []) h => nomatch h
  | mk (.mk (_::_)) _ => eq_of_data_eq rfl

theorem get_cons_zero (a : α) (x : SizedArray α n) {hi : 0 < n+1} : (cons a x)[0]'hi = a := by
  show (cons a x).val[0]'((cons a x).size_eq.symm ▸ hi) = a
  simp only [Array.getElem_eq_data_get]; dsimp [cons]

theorem get_cons_succ (a : α) (x : SizedArray α n) (i : Nat) {hi₁ : i+1 < n+1} {hi₂ : i < n} : (cons a x)[i+1] = x[i] := by
  show (cons a x).val[i+1]'((cons a x).size_eq.symm ▸ hi₁) = x.val[i]'(x.size_eq.symm ▸ hi₂)
  simp only [Array.getElem_eq_data_get]; dsimp [cons]

/-- Insert an element to the tail of an array. -/
def push (x : SizedArray α n) (a : α) : SizedArray α (n+1) :=
  ⟨x.val.push a, x.val.size_push a ▸ congrArg Nat.succ x.size_eq⟩

/-- Remove the last element. -/
def pop (x : SizedArray α (n+1)) : SizedArray α n :=
  ⟨x.val.pop, x.val.size_pop ▸ congrArg (·-1) x.size_eq⟩

/-- Get the last element of an array. -/
def back (x : SizedArray α (n+1)) : α :=
  x[n]'(n.lt_succ_self)

theorem back_eq_back'_val (x : SizedArray α (n+1)) : x.back = x.val.back' (x.size_eq.symm ▸ n.zero_lt_succ) := by
  dsimp [back, Array.back']; simp only [x.size_eq]; rfl

theorem push_pop_back (x : SizedArray α (n+1)) : .push x.pop x.back = x :=
  val_inj $
    show x.val.pop.push x.back = x.val
    from x.back_eq_back'_val ▸ x.val.push_pop_back' _

theorem get_push (x : SizedArray α n) (a : α) (i : Nat) {hi : i < n+1} : (x.push a)[i] = if h : i < n then x[i] else a :=
  (Array.get_push' a x.val i (x.val.size_push a ▸ x.size_eq.symm ▸ hi)).trans $
    dite_congr (x.size_eq.symm ▸ rfl) (λ _ => rfl) (λ _ => rfl)

theorem push_cons_eq_cons_push (a₁ a₂ : α) (x : SizedArray α n) : push (cons a₁ x) a₂ = cons a₁ (push x a₂) :=
  eq_of_data_eq $ by
    dsimp [push,cons, Array.push]; simp only [List.concat_eq_append]; rfl

/-- Induction principle on `SizedArray α n` based on `SizedArray.empty` as the base case and `SizedArray.cons` as the induction step. This version takes the major premise in the last argument; cf. `SizedArray.cons_induction_on`. -/
@[elab_as_elim]
theorem cons_induction {motive : (n : Nat) → SizedArray α n → Prop}
  (empty : motive 0 empty)
  (cons : {n : Nat} → (a : α) → (x : SizedArray α n) → motive n x → motive (n+1) (x.cons a))
  {n : Nat} (x : SizedArray α n) : motive n x :=
  x |> n.rec (fun | .empty => empty) λ _ IH x =>
    x.cons_head_tail ▸ cons x.head x.tail (IH x.tail)

/-- Induction principle on `SizedArray α n` based on `SizedArray.empty` as the base case and `SizedArray.cons` as the induction step. This version takes the major premise in the first argument; cf. `SizedArray.cons_induction`. -/
@[elab_as_elim]
theorem cons_induction_on {motive : (n : Nat) → SizedArray α n → Prop} {n : Nat} (x : SizedArray α n)
  (empty : motive 0 empty)
  (cons : {n : Nat} → (a : α) → (x : SizedArray α n) → motive n x → motive (n+1) (x.cons a))
  : motive n x :=
  x.cons_induction empty cons

/-- Simultaneous induction on two terms of `SizedArray α n` using `SizedArray.cons_induction_on`. -/
@[elab_as_elim]
theorem cons_induction_on₂ {motive : (n : Nat) → SizedArray α n → SizedArray β n → Prop} {n : Nat} (x : SizedArray α n) (y : SizedArray β n)
  (empty : motive 0 empty empty)
  (cons : {n : Nat} → (a : α) → (x : SizedArray α n) → (b : β) → (y : SizedArray β n) → motive n x y → motive (n+1) (x.cons a) (y.cons b))
  : motive n x y :=
  y |> x.cons_induction (fun | .empty => empty) λ a x IH y =>
    y.cons_head_tail ▸ cons a x y.head y.tail (IH y.tail)

/-- Induction principle on `SizedArray α n` based on `SizedArray.empty` as the base case and `SizedArray.push` as the induction step. This version takes the major premise in the last argument; cf. `SizedArray.push_induction_on`. -/
@[elab_as_elim]
theorem push_induction {motive : (n : Nat) → SizedArray α n → Prop}
  (empty : motive 0 empty)
  (push : {n : Nat} → (x : SizedArray α n) → (a : α) → motive n x → motive (n+1) (x.push a))
  {n : Nat} (x : SizedArray α n) : motive n x :=
  x |> n.rec (fun | .empty => empty) λ _ IH x =>
    x.push_pop_back ▸ push x.pop x.back (IH x.pop)

/-- Induction principle on `SizedArray α n` based on `SizedArray.empty` as the base case and `SizedArray.push` as the induction step. This version takes the major premise in the last argument; cf. `SizedArray.push_induction_on`. -/
@[elab_as_elim]
theorem push_induction_on {motive : (n : Nat) → SizedArray α n → Prop} {n : Nat} (x : SizedArray α n) 
  (empty : motive 0 empty)
  (push : {n : Nat} → (x : SizedArray α n) → (a : α) → motive n x → motive (n+1) (x.push a))
  : motive n x :=
  x.push_induction empty push

/-- Simultaneous induction on two terms of `SizedArray α n` using `SizedArray.push_induction_on`. -/
@[elab_as_elim]
theorem push_induction_on₂ {motive : (n : Nat) → SizedArray α n → SizedArray α n → Prop} {n : Nat} (x y : SizedArray α n)
  (empty : motive 0 empty empty)
  (push : {n : Nat} → (x y : SizedArray α n) → (a b : α) → motive n x y → motive (n+1) (x.push a) (y.push b))
  : motive n x y :=
  y |> x.push_induction (fun | .empty => empty) λ x a IH y =>
    y.push_pop_back ▸ push x y.pop a y.back (IH y.pop)

end Basic


/-! ## Declaration about `SizedArray.set` -/

section Set

variable {α : Type u} {n : Nat}

@[inline]
def set (x : SizedArray α n) (i : @& Fin n) (v : α) : SizedArray α n :=
  ⟨x.val.set (i.cast x.size_eq.symm) v, (x.val.size_set _ v).trans x.size_eq⟩

@[inline]
def uset (x : SizedArray α n) (i : @& USize) (v : α) (h : i.toNat < n) : SizedArray α n :=
  ⟨x.val.uset i v (x.size_eq.symm ▸ h), (x.val.size_uset v i _).trans x.size_eq⟩

@[simp]
theorem uset_eq_set (x : SizedArray α n) {i : USize} {v : α} {h : i.toNat < n} : x.uset i v h = x.set ⟨i.val,h⟩ v :=
  rfl

@[simp]
theorem get_set_eq (x : SizedArray α n) (i : Fin n) (v : α) : (x.set i v)[i] = v :=
  Array.get_set_eq x.val _ v

theorem get_set_ne (x : SizedArray α n) (i : Fin n) {j : Nat} (v : α) (hj : j < n) (h : i.val ≠ j) : (x.set i v)[j] = x[j] :=
  Array.get_set_ne x.val _ v (x.size_eq.symm ▸ hj) h

end Set


/-! ## Declaration about `SizedArray.replicate` -/

section Replicate

variable {α : Type u}

/-- `replicate n a` construct a sized array of `n` copies of `a` -/
def replicate (n : Nat) (a : α) : SizedArray α n :=
  ⟨Array.mkArray n a, Array.size_mkArray n a⟩

theorem replicate_zero {a : α} : replicate 0 a = empty :=
  rfl

theorem replicate_succ_eq_cons {n : Nat} {a : α} : replicate (n+1) a = cons a (replicate n a) :=
  rfl

/-- Each entry of `replicate n a` equals `a` -/
theorem get_replicate {n : Nat} {a : α} {i : Nat} {h : i < n} : (replicate n a)[i] = a :=
  match n, i with
  | 0, _ => nomatch h
  | n+1, 0 => rfl
  | n+1, i+1 => by
    simp only [replicate_succ_eq_cons, get_cons_succ (hi₁:=h) (hi₂:=Nat.lt_of_succ_lt_succ h)]
    exact get_replicate (a:=a) (i:=i) (h:=Nat.lt_of_succ_lt_succ h)

theorem replicate_succ_eq_push {n : Nat} {a : α} : replicate (n+1) a = (replicate n a).push a :=
  ext _ _ fun i hi => by
    simp only [get_replicate, get_push]
    apply dite (i < n) <;> (intro h; simp only [h]; rfl)

end Replicate


/-! ## Declaration about `SizedArray.foldl` and `SizedArray.foldr` -/

section Fold

variable {α : Type u} {β : Type v} {n : Nat}

@[inline]
def foldlM {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (x : SizedArray α n) : m β :=
  x.val.foldlM f init

theorem foldlM_push {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : β → α → m β) (init : β) (x : SizedArray α n) (a : α) : foldlM f init (x.push a) = (foldlM f init x >>= λ b => f b a) :=
  x.val.foldlM_push f init a

theorem foldlM_cons {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : β → α → m β) (init : β) (a : α) (x : SizedArray α n) : foldlM f init (.cons a x) = (f init a >>= λ b => foldlM f b x) :=
  x.val.foldlM_cons f init a

@[inline]
def foldl (f : β → α → β) (init : β) (x : SizedArray α n) : β :=
  x.val.foldl f init

theorem foldl_eq_foldlM (f : β → α → β) (init : β) (x : SizedArray α n) : x.foldl f init = Id.run (x.foldlM f init) :=
  rfl

@[inline]
def foldrM {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (x : SizedArray α n) : m β :=
  x.val.foldrM f init

@[inline]
def foldr (f : α → β → β) (init : β) (x : SizedArray α n) : β :=
  x.val.foldr f init

theorem foldr_eq_foldrM (f : α → β → β) (init : β) (x : SizedArray α n) : x.foldr f init = Id.run (x.foldrM f init) :=
  rfl

/-- Implementation of `SizedArray.foldlMIdx`. -/
@[inline]
unsafe def foldlMIdxUnsafe {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) (x : SizedArray α n) : m (β n) :=
  let nu := USize.ofNat n
  let rec @[specialize] loop (i : USize) (j : Nat) (b : β j) : m (β n) := do
    if i == nu then
      pure (lcProof (α:=j=n) ▸ b)
    else
      loop (i+1) (j+1) (← f j b (x.val.uget i lcProof))
  loop 0 0 init

/-
Yet another unsafe version of `SizedArray.foldlMIdx`. This version uses `Array.foldlMUnsafe`.

:::note warn
This function does not necessarily agree with `foldlMIdxUnsafe` unless the monad `m` satisfies monad laws; i.e. `LawfulMonad m`.
:::
-/
@[inline]
unsafe def foldlMIdxUnsafe' {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) (x : SizedArray α n) : m (β n) :=
  let f': (i : Nat) × β i → α → m ((i : Nat) × β i) :=
    λ bi a => f bi.1 bi.2 a >>= λ b => pure ⟨bi.1+1, b⟩
  x.val.foldlMUnsafe f' ⟨0,init⟩ >>= λ bi => pure (lcProof (α:=bi.1=n) ▸ bi.2)

/--
Analogue of `SizedArray.foldlM` while this version passes indices to the operator and take a value in a target type dependent on the size. This is a reference implementation; for executable codes, see `foldlMIdxUnsafe`.
-/
--@[implemented_by foldlMIdxUnsafe]
def foldlMIdx {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) (x : SizedArray α n) : m (β n) :=
  let rec loop (i : Nat) (hi : i ≤ n) (b : β i) : m (β n) := do
    if h : i = n then
      pure (h ▸ b)
    else
      have : i < n := Nat.lt_of_le_of_ne hi h
      loop (i+1) this (← f i b x[i])
  loop 0 n.zero_le init
termination_by loop => n-i

theorem foldlMIdx_empty {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) : foldlMIdx f init empty = pure init := by
  unfold foldlMIdx; unfold foldlMIdx.loop
  exact dif_pos rfl

theorem foldlMIdx.loop_cons_succ {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (a : α) (x : SizedArray α n) (i : Nat) (h₁ : i+1 ≤ n+1) (h₂ : i ≤ n) (b : β (i+1)) : foldlMIdx.loop f (.cons a x) (i+1) h₁ b = foldlMIdx.loop (β:=β ∘ Nat.succ) (λ i b => f (i+1) b) x i h₂ b := by
  unfold loop
  if h : i = n then
    cases h; rw [dif_pos rfl, dif_pos rfl]
  else
    have : i < n := Nat.lt_of_le_of_ne h₂ h
    simp only [dif_neg (Nat.ne_of_lt this), dif_neg (Nat.ne_of_lt (Nat.succ_lt_succ this))]
    rw [get_cons_succ]
    exact bind_congr λ b => foldlMIdx.loop_cons_succ f a x (i+1) (Nat.succ_lt_succ this) this b
termination_by _ => n-i

theorem foldlMIdx_cons {β : Nat → Type v} {m : Type v → Type w} [Monad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) (a : α) (x : SizedArray α n) : foldlMIdx f init (.cons a x) = (f 0 init a >>= λ b => foldlMIdx (β:=λ i => β i.succ) (λ i b => f i.succ b) b x) := by
  unfold foldlMIdx
  conv => lhs; unfold foldlMIdx.loop; simp only [dif_neg n.succ_ne_zero.symm]
  apply bind_congr; intro b
  exact foldlMIdx.loop_cons_succ f a x 0 _ _ b

theorem foldlM_eq_foldlMIdx {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (x : SizedArray α n) : foldlM f init x = foldlMIdx (β:=λ _ => β) (λ _ => f) init x := by
  unfold foldlM; rw [Array.foldlM_eq_foldlM_data']
  induction x using cons_induction generalizing init with
  | empty => rfl
  | cons a x IH =>
    conv => lhs; dsimp [cons]
    rw [foldlMIdx_cons]
    apply bind_congr; intro b
    exact IH b

theorem foldlMIdx_push {β : Nat → Type v} {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : (i : Nat) → β i → α → m (β (i+1))) (init : β 0) (x : SizedArray α n) (a : α) : foldlMIdx f init (x.push a) = (foldlMIdx f init x >>= λ b => f n b a) := by
  induction x using cons_induction generalizing β f init with
  | empty =>
    conv =>
      lhs; unfold foldlMIdx; unfold foldlMIdx.loop
      rw [dif_neg (by decide : 0 ≠ 0+1)]
      change f 0 init a >>= foldlMIdx.loop f (push empty a) 1 (.refl)
      rhs; ext; unfold foldlMIdx.loop; rw [dif_pos rfl]
    conv => rhs; rw [foldlMIdx_empty, pure_bind]
    rw [bind_pure]
  | cons a₁ x IH =>
    rw [push_cons_eq_cons_push]
    simp only [foldlMIdx_cons f init a₁]
    rw [bind_assoc]
    apply bind_congr; intro b
    exact IH ..

end Fold


/-! ## Declaration about `SizedArray.map`-/

section Map

variable {α : Type u} {β : Type v} {γ : Type w} {n : Nat}

/-- Implementation of `SizedArray.mapM`. Since Lean compiler erases `Sort 0` (aka `Prop`) terms, the type `SizedArray` is identified with `Array` in the executable code provided the size `n` is known. That is why the cast `unsafeCast` succeeds. -/
@[inline]
unsafe def mapMUnsafe {m : Type v → Type w} [Monad m] (f : α → m β) (x : SizedArray α n) : m (SizedArray β n) :=
  unsafeCast <| x.val.mapMUnsafe f

/--
Reference implementation for `SizedArray.mapM`.

:::note warn
Prior to the commit 3104c223d84006484271962a45157c628e5891b7, Lean's core has an inconsistent reference implementation for `Array.mapM`.
The implementation of `SizedArray.mapM` is based on the fixed version, so it is not necessarily compatible with `Array.mapM` in the version older than the commit (unless the monad is `LawfulMonad`).
:::
-/
@[implemented_by mapMUnsafe]
def mapM {m : Type v → Type w} [Monad m] (f : α → m β) (x : SizedArray α n) : m (SizedArray β n) :=
  let rec loop (i : Nat) (hi : i ≤ n) (r : SizedArray β i) : m (SizedArray β n) := do
    if hlt : i < n then
      loop (i+1) hlt (r.push (← f x[i]))
    else
      have : i = n := (Nat.eq_or_lt_of_le hi).elim id (λ h => absurd h hlt)
      pure (this ▸ r)
  loop 0 n.zero_le (mkEmpty n)
termination_by loop => n - i

/--
Implementation of `SizedArray.mapIdxM` based on `Array.mapM`.

@TODO take a benchmark to ensure this is in fact faster than `Array.mapIdxM` which has a safe and pure implementation.
-/
@[inline]
unsafe def mapMIdxUnsafe {m : Type v → Type w} [Monad m] (f : Fin n → α → m β) (x : SizedArray α n) : m (SizedArray β n) :=
  let nu := USize.ofNat n
  let rec @[specialize] loop (i : USize) (j : Nat) (r : Array NonScalar) : m (Array PNonScalar.{v}) := do
    if i == nu then
      pure (unsafeCast r)
    else
     let v    := r.uget i lcProof
     -- Replace r[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let r    := r.uset i default lcProof
     let vNew ← f ⟨j, lcProof⟩ (unsafeCast v)
     loop (i+1) (j+1) (r.uset i (unsafeCast vNew) lcProof)
  unsafeCast <| loop 0 (unsafeCast x.val)

/-- Similar to `SizedArray.mapM` while this version passes indices to the unary operator. The definition body is a reference implementation; for the actual implementation, see `mapMIdxUnsafe`. -/
@[implemented_by mapMIdxUnsafe]
def mapMIdx {m : Type v → Type w} [Monad m] (f : Fin n → α → m β) (x : SizedArray α n) : m (SizedArray β n) :=
  let rec loop (i : Nat) (hi : i ≤ n) (r : SizedArray β i) : m (SizedArray β n) := do
    if h : i = n then
      pure (h ▸ r)
    else
      have : i < n := Nat.lt_of_le_of_ne hi h
      let r := r.push (← f ⟨i,this⟩ x[i])
      loop (i+1) this r
  loop 0 n.zero_le (mkEmpty n)
termination_by loop => n-i

theorem mapM_empty {m : Type v → Type w} [Monad m] (f : α → m β) : mapM f empty = pure empty :=
  rfl

theorem mapM.loop_cons_succ {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : α → m β) (a : α) (x : SizedArray α n) (i : Nat) {hi₁ : i+1 ≤ n+1} {hi₂ : i ≤ n} (b : β) (r : SizedArray β i) : mapM.loop f (cons a x) (i+1) hi₁ (cons b r) = (mapM.loop f x i hi₂ r >>= λ y => pure (cons b y)) := by
  cases Nat.eq_or_lt_of_le hi₂ with
  | inl heq =>
    cases heq; unfold loop; simp only [Nat.lt_irrefl, dif_neg, pure_bind]
  | inr hlt =>
    conv =>
      lhs; unfold loop
      rw [dif_pos (Nat.succ_lt_succ hlt)]
      rw [get_cons_succ a x (hi₁:=Nat.succ_lt_succ hlt) (hi₂:=hlt)]
      rhs; ext b'; rw [push_cons_eq_cons_push]
      rw [mapM.loop_cons_succ f a x (hi₁:=Nat.succ_lt_succ hlt) (hi₂:=hlt) b (r.push b')]
    conv =>
      rhs; unfold loop; rw [dif_pos hlt, bind_assoc]
termination_by _ => n-i

theorem mapM_cons {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : α → m β) (a : α) (x : SizedArray α n) : mapM f (cons a x) = (f a >>= λ b => mapM f x >>= λ y => pure (cons b y)) := by
  conv =>
    lhs; unfold mapM; unfold mapM.loop
    rw [dif_pos n.zero_lt_succ, get_cons_zero a x]
    rhs; ext b; change mapM.loop f (cons a x) (0+1) (n.zero_lt_succ) (cons b empty)
  apply bind_congr; intro b
  exact mapM.loop_cons_succ f a x (hi₁:=n.zero_lt_succ) b empty

theorem mapM_push {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : α → m β) (x : SizedArray α n) (a : α) : mapM f (x.push a) = (mapM f x >>= λ y => f a >>= λ b => pure (y.push b)) :=
  x.cons_induction
    (by
      rw [mapM_empty, pure_bind]
      unfold mapM; unfold mapM.loop; unfold mapM.loop
      simp only [(by decide : 0 < 0+1), (by decide : ¬ (0 + 1 < 0+1)), dif_pos, dif_neg]
      rfl
    )
    λ a x IH => by
      simp only [push_cons_eq_cons_push, mapM_cons, bind_assoc, IH, pure_bind]

theorem mapMIdx_empty {m : Type v → Type w} [Monad m] (f : Fin 0 → α → m β) : mapMIdx f empty = pure empty := by
  unfold mapMIdx; unfold mapMIdx.loop; rw [dif_pos rfl]; rfl

theorem mapMIdx.loop_cons_succ {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m β) (a : α) (x : SizedArray α n) (i : Nat) {hi₁ : i+1 ≤ n+1} {hi₂ : i ≤ n} (b : β) (r : SizedArray β i) : mapMIdx.loop f (cons a x) (i+1) hi₁ (cons b r) = (mapMIdx.loop (f ∘ Fin.succ) x i hi₂ r >>= λ y => pure (cons b y)) := by
  cases Nat.eq_or_lt_of_le hi₂ with
  | inl heq =>
    cases heq; unfold loop; simp only [dif_pos]; rw [pure_bind]
  | inr hlt =>
    unfold loop
    simp only [Nat.ne_of_lt hlt, Nat.ne_of_lt (Nat.succ_lt_succ hlt), dif_neg]
    rw [bind_assoc]
    apply bind_congr; intro b'
    rw [push_cons_eq_cons_push]
    exact mapMIdx.loop_cons_succ f a x (i+1) b (push r b')
termination_by _ => n-i

theorem mapMIdx_cons {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m β) (a : α) (x : SizedArray α n) : mapMIdx f (cons a x) = (f ⟨0,n.zero_lt_succ⟩ a >>= λ b => mapMIdx (f ∘ Fin.succ) x >>= λ y => pure (cons b y)) := by
  conv =>
    lhs; unfold mapMIdx; unfold mapMIdx.loop
    rw [dif_neg n.succ_ne_zero.symm]; dsimp
    rhs; ext b; change mapMIdx.loop f (cons a x) 1 n.zero_lt_succ (cons b empty)
    rw [mapMIdx.loop_cons_succ f a x 0 b empty]

theorem mapMIdx_push {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m β) (x : SizedArray α n) (a : α) : mapMIdx f (push x a) = (mapMIdx (λ i => f ⟨i.1,.step i.2⟩) x >>= λ y => f ⟨n,n.lt_succ_self⟩ a >>= λ b => pure (push y b)) :=
  f |> x.cons_induction
    (λ f => by
      unfold mapMIdx; unfold mapMIdx.loop
      rw [dif_neg (c:=0=0+1) (by decide), dif_pos rfl]; dsimp
      rw [pure_bind]; apply bind_congr; intro b
      unfold mapMIdx.loop; rw [dif_pos rfl]
      rfl
    )
    λ a x IH f => by
      simp only [push_cons_eq_cons_push, mapMIdx_cons, bind_assoc, pure_bind]
      apply bind_congr; intro b
      rw [IH]; simp only [bind_assoc, pure_bind]
      rfl

theorem mapM_eq_mapMIdx {m : Type v → Type w} [Monad m] [LawfulMonad m] (f : α → m β) (x : SizedArray α n) : mapM f x = mapMIdx (λ _ => f) x :=
  x.cons_induction (mapM_empty f) λ a x IH => by
    rw [mapM_cons, mapMIdx_cons, IH]; rfl

def map (f : α → β) (x : SizedArray α n) : SizedArray β n :=
  ⟨x.val.map f, Array.size_map' f x.val ▸ x.size_eq⟩

def mapIdx (f : Fin n → α → β) (x : SizedArray α n) : SizedArray β n :=
  Id.run <| mapMIdx f x

@[simp]
theorem get_map (f : α → β) (x : SizedArray α n) (i : Nat) {hi : i < n} : (x.map f)[i] = f (x[i]) :=
  show (x.val.map f)[i]'(Array.size_map' f x.val ▸ x.size_eq.symm ▸ hi) = f (x.val[i]'(x.size_eq.symm ▸ hi))
  from x.val.getElem_map' f i _

@[simp]
theorem map_empty (f : α → β) : map f empty = empty :=
  rfl

theorem map_cons (f : α → β) (a : α) (x : SizedArray α n) : map f (x.cons a) = .cons (f a) (map f x) :=
  val_inj $ Array.map_cons f a x.val

theorem map_push (f : α → β) (x : SizedArray α n) (a : α) : map f (x.push a) = .push (x.map f) (f a) :=
  val_inj $ Array.map_push f x.val a

theorem map_id (x : SizedArray α n) : x.map id = x :=
  x.push_induction rfl λ x a IH => by rw [map_push, IH]; rfl

theorem comp_map (f : α → β) (g : β → γ) (x : SizedArray α n) : x.map (g ∘ f) = (x.map f).map g :=
  x.push_induction rfl λ x a IH => by simp only [map_push, IH]; rfl

theorem map_eq_mapM (f : α → β) (x : SizedArray α n) : x.map f = x.mapM (m:=Id) f :=
  x.push_induction rfl λ x a IH => by rw [map_push, mapM_push, IH]; rfl

@[simp]
theorem mapIdx_empty (f : Fin 0 → α → β) : mapIdx f empty = empty :=
  rfl

theorem mapIdx_cons (f : Fin (n+1) → α → β) (a : α) (x : SizedArray α n) : mapIdx f (cons a x) = cons (f ⟨0,n.zero_lt_succ⟩ a) (mapIdx (f ∘ Fin.succ) x) :=
  mapMIdx_cons (m:=Id) f a x

theorem mapIdx_push (f : Fin (n+1) → α → β) (x : SizedArray α n) (a : α) : mapIdx f (push x a) = push (mapIdx (λ i => f ⟨i.1,.step i.2⟩) x) (f ⟨n,n.lt_succ_self⟩ a):=
  mapMIdx_push (m:=Id) f x a

theorem map_eq_mapIdx (f : α → β) (x : SizedArray α n) : map f x = mapIdx (λ _ => f) x :=
  (map_eq_mapM f x).trans (mapM_eq_mapMIdx (m:=Id) f x)

theorem get_mapIdx (f : Fin n → α → β) (x : SizedArray α n) (i : Nat) {hi : i < n} : (x.mapIdx f)[i] = f ⟨i,hi⟩ x[i] := by
  induction x using cons_induction generalizing i with
  | empty => cases hi
  | cons a x IH =>
    simp only [mapIdx_cons]
    cases i with
    | zero => simp only [Nat.zero_eq, get_cons_zero]
    | succ i =>
      simp only [Nat.zero_eq, Nat.succ_eq_add_one]
      rw [get_cons_succ (hi₂:=Nat.lt_of_succ_lt_succ hi)]
      rw [get_cons_succ (hi₂:=Nat.lt_of_succ_lt_succ hi)]
      exact IH ..

end Map


/-! ## Declaration about `SizedArray.modifyM` -/
section Modify

variable {m : Type u → Type v} [Monad m] {α : Type u} {n : Nat}

/--
Implementation of `SizedArray.modifyM`.

Note that, in view of the runtime environment, we may assume `a.size < USize.size` for any `a : Array α` since its underlying data is nothing but a memory array on the heap.
In particular, if `x : SizedArray α n`, this implies `n < USize.size` so that `i < n → i < USize.size`.
This is why the `lcProof` below is "harmless".
-/
@[inline]
unsafe def modifyMUnsafe (x : SizedArray α n) (i : Fin n) (f : α → m α) : m (SizedArray α n) := do
  let idx : USize := ⟨i, lcProof⟩
  let v := x.val.uget idx (x.size_eq.symm ▸ i.2)
  -- Replace x[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
  -- Note: we assume that arrays have a uniform representation irrespective
  -- of the element type, and that it is valid to store `box(0)` in any array.
  let x' := x.uset idx (unsafeCast ()) i.2
  let v ← f v
  return x'.uset idx v i.2

/--
`modifyM x i f` modifies the `i`-th entry of `x : SizedArray α n` with an update function `f : α → m α`.
See also `SizedArray.modify` in the special case `m = Id`.

:::note info
In contrast to `Array.modifyM`, the index `i` is of type `Fin n` instead of `Nat`.
:::
-/
@[implemented_by modifyMUnsafe]
def modifyM (x : SizedArray α n) (i : Fin n) (f : α → m α) : m (SizedArray α n) := do
  let v := x[i]
  let v ← f v
  return x.set i v

/--
`modify x i f` modifies the `i`-th entry of `x : SizedArray α n` with an update function `f : α → α`.
For updates in a monadic context `m`, see also `SizedArray.modifyM`.

:::note info
In contrast to `Array.modify`, the index `i` is of type `Fin n` instead of `Nat`.
:::
-/
@[inline]
def modify (x : SizedArray α n) (i : Fin n) (f : α → α) : SizedArray α n :=
  Id.run <| modifyM x i f

theorem modify_eq_set_get (x : SizedArray α n) (i : Fin n) (f : α → α) : x.modify i f = x.set i (f <| x[i.val]'i.isLt) :=
  rfl

@[simp]
theorem get_modify_eq (x : SizedArray α n) (i : Fin n) (f : α → α) : (x.modify i f)[i] = f x[i] :=
  show (x.set i (f x[i]))[i] = f x[i]
  from x.get_set_eq i (f x[i])

theorem get_modify_ne (x : SizedArray α n) (i : Fin n) {j : Nat} (f : α → α) (hj : j < n) (h : i.val ≠ j) : (x.modify i f)[j] = x[j] :=
  show (x.set i (f x[i]))[j] = x[j]
  from x.get_set_ne i (f x[i]) hj h

end Modify


/-! ## Declaration about `SizedArray.zipWith` -/

section ZipWith

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type uu} {n : Nat}

/-- The unsafe implementation of `SizedArray.zipWith`. -/
@[inline]
unsafe def zipWithUnsafe (x : @& SizedArray α n) (y : SizedArray β n) (f : α → β → γ) : SizedArray γ n :=
  let nu := USize.ofNat n
  let rec @[specialize] loop (i : USize) (r : Array NonScalar) : Array PNonScalar.{w} :=
    if i == nu then
      unsafeCast r
    else
      let v := r.uget i lcProof
      -- Replace r[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
      -- Note: we assume that arrays have a uniform representation irrespective
      -- of the element type, and that it is valid to store `box(0)` in any array.
      let r    := r.uset i default lcProof
      let vNew := f (x.val.uget i lcProof) (unsafeCast v)
      loop (i+1) (r.uset i (unsafeCast vNew) lcProof)
  unsafeCast <| loop 0 (unsafeCast y)

/-- A binary analogue of `SizedArray.map`. -/
def zipWith (x : SizedArray α n) (y : SizedArray β n) (f : α → β → γ) : SizedArray γ n :=
  mapIdx (λ i => f x[i]) y

@[simp]
theorem zipWith_empty (f : α → β → γ) : zipWith empty empty f = empty :=
  mapIdx_empty _

theorem zipWith_cons (a : α) (x : SizedArray α n) (b : β) (y : SizedArray β n) (f : α → β → γ) : zipWith (cons a x) (cons b y) f = cons (f a b) (zipWith x y f) := by
  unfold zipWith; rw [mapIdx_cons]
  apply congrArg (cons (f a b)); apply congrFun; apply congrArg
  funext i; cases i with | mk i h => rfl

theorem zipWith_push (x : SizedArray α n) (a : α) (y : SizedArray β n) (b : β) (f : α → β → γ) : zipWith (push x a) (push y b) f = push (zipWith x y f) (f a b) := by
  unfold zipWith; rw [mapIdx_push]
  conv =>
    lhs; arg 2
    change f ((push x a)[n]'n.lt_succ_self) b
    rw [get_push, dif_neg n.lt_irrefl]
  apply congrFun; apply congrArg
  apply congrFun; apply congrArg
  funext i; cases i with | mk i h =>
  apply congrArg
  show (push x a)[i]'(.step h) = x[i]'h
  rw [get_push, dif_pos h]

@[simp]
theorem get_zipWith {x : SizedArray α n} {y : SizedArray β n} {f : α → β → γ} {i : Nat} {h : i < n} : (zipWith x y f)[i] = f x[i] y[i] := by
  induction x, y using cons_induction_on₂ generalizing i with
  | empty => cases h
  | cons a x b y IH =>
    simp only [zipWith_cons]
    cases i with
    | zero => simp only [get_cons_zero]
    | succ i =>
      simp only [Nat.succ_eq_add_one, get_cons_succ (hi₁:=h) (hi₂:=Nat.lt_of_succ_lt_succ h)]
      exact IH

theorem zipWith_flip (x : SizedArray α n) (y : SizedArray β n) (f : α → β → γ) : zipWith y x (flip f) = zipWith x y f :=
  cons_induction_on₂ x y (zipWith_empty f) λ a x b y IH => by
    simp only [zipWith_cons]
    exact congrArg (cons (f a b)) IH

def zipWith₃ (x : SizedArray α n) (y : SizedArray β n) (z : SizedArray γ n) (f : α → β → γ → δ) : SizedArray δ n :=
  mapIdx (λ (i : Fin n) => f x[i.val] y[i.val]) z

def zipWith₃_cons (a : α) (x : SizedArray α n) (b : β) (y : SizedArray β n) (c : γ) (z : SizedArray γ n) (f : α → β → γ → δ) : zipWith₃ (cons a x) (cons b y) (cons c z) f = cons (f a b c) (zipWith₃ x y z f) := by
  unfold zipWith₃; simp only [mapIdx_cons, get_cons_zero]
  apply congrArg (cons (f a b c)); apply congrFun; apply congrArg
  funext i; dsimp [Fin.succ]
  rw [get_cons_succ (hi₂:=i.isLt), get_cons_succ (hi₂:=i.isLt)]

theorem zipWith_zipWith_left {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (x : SizedArray α₁ n) (y : SizedArray α₂ n) (f : α₁ → α₂ → β₁) (z : SizedArray β₂ n) (g : β₁ → β₂ → γ) : zipWith (zipWith x y f) z g = zipWith₃ x y z (λ a₁ a₂ b₂ => g (f a₁ a₂) b₂) :=
  z |> cons_induction_on₂ x y (λ .empty => zipWith_empty g) λ a x b y IH z => by
    rw [← z.cons_head_tail]
    simp only [zipWith_cons, zipWith₃_cons]
    rw [IH z.tail]

theorem zipWith_zipWith_right {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (x : SizedArray α₁ n) (y : SizedArray β₁ n) (z : SizedArray β₂ n) (f : β₁ → β₂ → α₂) (g : α₁ → α₂ → γ) : zipWith x (zipWith y z f) g = zipWith₃ x y z (λ a b c => g a (f b c)) :=
  x |> cons_induction_on₂ y z (λ .empty => zipWith_empty g) λ b y c z IH x => by
    rw [← x.cons_head_tail]
    simp only [zipWith_cons, zipWith₃_cons]
    rw [IH x.tail]

end ZipWith


/-! ## Declarations about `SizedArray.ofFn` -/

section OfFn

variable {α : Type u} {n : Nat}

/-- Given `f : Fin n → α`, `SizedArray.ofFn f` is the array whose `i`-th entry is `f i`. -/
@[inline]
def ofFn (f : Fin n → α) : SizedArray α n :=
  ⟨Array.ofFn f, Array.size_ofFn f⟩

theorem get_ofFn (f : Fin n → α) (i : Nat) (h : i < n) : (ofFn f)[i] = f ⟨i,h⟩ :=
  Array.getElem_ofFn' f i ((Array.size_ofFn f).symm ▸ h)

end OfFn


/-! ## Change of indexing sets -/

section Index

variable {α : Type u} {m n : Nat}

/-- For `f : Fin m → Fin n` and `x : SizedArray α n`, `SizedArray.pullback f x` is the array whose `i`-th entry is `x[f i]`. -/
def pullback (f : Fin m → Fin n) (x : SizedArray α n) : SizedArray α m :=
  ofFn fun i => x[f i]

@[simp]
theorem get_pullback (f : Fin m → Fin n) (x : SizedArray α n) (i : Nat) (h : i < m) : (x.pullback f)[i] = x[f ⟨i,h⟩] :=
  get_ofFn (fun i => x[f i]) i h

end Index

end SizedArray

