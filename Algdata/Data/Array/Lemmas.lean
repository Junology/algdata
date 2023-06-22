/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Basic
import Std.Data.Array.Lemmas

import Algdata.Init.Nat
import Algdata.Data.Nat.Rec
import Algdata.Data.List.Basic

/-!

# Miscellaneous lemmas for `Array`

Lemmas around `Array` including `Classical`-free variants of those in Std library.

-/

namespace Array

universe u v w

variable {α : Type u}

/-!
## Equality
-/

/-- The equality of `Array`. -/
protected
theorem eq : ∀ (x y : Array α), x.data = y.data → x=y
| Array.mk _, Array.mk _, rfl => rfl


/-!
## `Array.size`
-/

@[simp]
theorem size_nil {α : Type _} : @Array.size α #[] = 0 := rfl

@[simp]
theorem size_cons (a : α) (as : List α) : Array.size {data := a::as} = (Array.size {data := as}).succ := rfl

theorem size_eq_length_of_data (x : Array α) : x.size = x.data.length := rfl


/-!
## `Array.foldl`
-/

/-- Induction step of `foldl` in terms of `Array.data`. -/
theorem foldl_cons {β : Type v} (f : β → α → β) (init : β) (a : α) (as : List α) : foldl f init {data := a::as} = foldl f (f init a) {data := as} := by
  rw [Array.foldl, Array.foldl]
  rw [Array.foldlM, Array.foldlM]
  rw [Id.run, Id.run]
  simp
  rw [foldlM.loop, dif_pos (Nat.zero_lt_succ _)]
  simp
  suffices t : ∀ v vs h l k w, foldlM.loop (m := Id) f {data := v::vs} vs.length.succ h l (k+1) w = foldlM.loop (m := Id) f {data := vs} vs.length (Nat.le_of_succ_le_succ h) l k w by
    rw [t]
    apply congrArg
    rfl
  intros v vs h l
  induction l with
  | zero =>
    intro k w
    rw [foldlM.loop, foldlM.loop]
    simp
    apply Decidable.byCases (p := k < vs.length)
    case h1 =>
      intro hpos
      rw [dif_pos hpos, dif_pos (Nat.succ_lt_succ hpos)]
    case h2 =>
      intro hneg
      have : ¬(k+1 < vs.length.succ) :=
        fun h' => hneg (Nat.lt_of_succ_lt_succ h')
      rw [dif_neg hneg, dif_neg this]
  | succ l' hi =>
    intro k w
    rw [foldlM.loop, foldlM.loop]
    apply Decidable.byCases (p := k < vs.length)
    case h1 =>
      intro hpos
      rw [dif_pos hpos, dif_pos (Nat.succ_lt_succ hpos)]
      simp
      rw [hi]
      apply congrArg
      rfl
    case h2 =>
      intro hneg
      have : ¬(k+1 < vs.length.succ) :=
        fun h' => hneg (Nat.lt_of_succ_lt_succ h')
      rw [dif_neg hneg, dif_neg this]

/-- `Classical`-free analogue of `Array.foldl_eq_foldl_data` in Std -/
theorem foldl_eq_foldl_data' {β : Type v} (f : α → β → α) (init : α) (arr : Array β) : foldl f init arr = List.foldl f init arr.data := by
  cases arr with | mk bs =>
  induction bs generalizing init
  case nil => rfl
  case cons b bs h_ind =>
    rw [foldl_cons, h_ind]
    rfl


/-!
## `Array.append`
-/

theorem cons_append_data (a : α) : ∀ (as : List α) (x : Array α), ({data := a::as} ++ x).data = a::({data := as} ++ x).data
| as, mk bs => by
  induction bs generalizing as with
  | nil => intros; rfl
  | cons b bs hi =>
    rw [←Array.append_eq_append, ←Array.append_eq_append]
    unfold Array.append
    rw [foldl_cons, foldl_cons]
    exact hi (as.concat b)

theorem append_nil : ∀ (x : Array α), x ++ #[] = x
| Array.mk [] => rfl
| Array.mk (_::_) => rfl

theorem append_cons : ∀ (x : Array α) (b : α) (bs : List α), x ++ {data := b::bs} = (x.push b) ++ {data := bs} := by
  intros x b bs
  rw [←Array.append_eq_append, ←Array.append_eq_append]
  unfold Array.append
  rw [foldl_cons]

/-- `Classical`-free analogue of `append_data` in Std4. -/
theorem append_data' (x y : Array α) : (x ++ y).data = x.data ++ y.data := by
  cases y with | mk bs =>
  induction bs generalizing x
  case nil =>
    conv =>
      change (x ++ #[]).data = x.data ++ []
      rw [append_nil]
    rw [List.append_nil]
  case cons b bs h_ind =>
    rw [append_cons, h_ind]
    conv => change (x.push b).data ++ bs = x.data ++ (b::bs)
    rw [push_data, ←List.append_cons]

theorem nil_append : ∀ (x : Array α), #[] ++ x = x
| Array.mk as => by
  induction as with
  | nil => rfl
  | cons a as hi =>
    rw [append_cons]
    have : #[].push a = {data :=[a]} := rfl
    rw [this]; clear this
    apply Array.eq
    rw [cons_append_data]
    rw [(_ : {data :=[]} = #[])]
    rw [hi]
    rfl

theorem append_push : ∀ (x y : Array α) (a : α), x ++ (y.push a) = (x ++ y).push a := by
  intro x y a
  cases y with | mk bs =>
  induction bs generalizing x
  case nil => rfl
  case cons b bs h_ind =>
    dsimp [Array.push, List.concat]
    rw [append_cons, append_cons]
    have : Array.mk (List.concat bs a) = Array.push {data := bs} a := rfl
    rw [this]
    exact h_ind (x.push b)

theorem append_assoc : ∀ (x y z : Array α), (x ++ y) ++ z = x ++ (y ++ z) := by
  intro x y z
  cases z with | mk cs =>
  induction cs generalizing y
  case nil => rfl
  case cons c cs h_ind =>
    rw [append_cons, append_cons, ←append_push]
    exact h_ind (y.push c)

theorem push_as_append (x : Array α) (a : α) : x.push a = x ++ #[a] := rfl

theorem append_size : ∀ (x y : Array α), (x ++ y).size = x.size + y.size
| mk as, y => by
  induction as with
  | nil =>
    have : mk (α:=α) [] = #[] := rfl
    rw [this, nil_append]
    rw [size_nil, Nat.zero_add]
  | cons a as hi =>
    rw [Array.size, cons_append_data, List.length]
    rw [Array.size, List.length]
    rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
    have : List.length ({data:=as} ++ y).data = ({data:=as} ++ y).size := rfl
    rw [this, hi]


/-!
## `Array.get` and `Array.set`
-/

theorem get_cons_succ (a : α) (as : List α) (n : Fin as.length): Array.get {data := a::as} n.succ = Array.get {data := as} n := by
  rw [Array.get, Array.get]
  cases n
  rfl

theorem get_cons_succ' (a : α) (as : List α) (n : Nat) {h : n.succ < as.length.succ} : Array.get {data := a::as} ⟨n.succ,h⟩ = Array.get {data := as} ⟨n,Nat.lt_of_succ_lt_succ h⟩ := by
  have : Fin.mk n.succ h = (Fin.mk n (Nat.lt_of_succ_lt_succ h)).succ := rfl
  rw [this]
  exact get_cons_succ a as ⟨n, Nat.lt_of_succ_lt_succ h⟩

theorem set_head (a : α) (as : List α) {h : 0 < as.length.succ} (v : α) : Array.set {data := a::as} ⟨0,h⟩ v = {data := v::as} := rfl

theorem set_cons_succ (a : α) (as : List α) (n : Fin as.length) (v : α) : Array.set {data := a::as} n.succ v = #[a] ++ (Array.set {data:=as} n v) := by
  apply Array.eq
  rw [Array.set, Array.set]
  rw [Fin.val_succ_eq_succ_val]
  rw [List.set]
  have : #[a] = {data:=a::[]} := rfl
  rw [this, cons_append_data]
  have : #[] = {data:=([] : List α)} := rfl
  rw [←this, nil_append]

theorem set_cons_succ' (a : α) (as : List α) (n : Nat) (h : n.succ < as.length.succ) (v : α) : Array.set {data:=a::as} ⟨n+1,h⟩ v = #[a] ++ Array.set {data:=as} ⟨n,Nat.lt_of_succ_lt_succ h⟩ v := by
  have : Fin.mk n.succ h = (Fin.mk n (Nat.lt_of_succ_lt_succ h)).succ := rfl
  rw [this]
  rw [set_cons_succ]


/-!
## `Array.zipWith`
-/

section zipWith

variable {β : Type v} {γ : Type w}

theorem zipWithAux_nil_first (f : α → β → γ) (x : Array β) (n : Nat) (z : Array γ) : Array.zipWithAux f #[] x n z = z := by
  rw [Array.zipWithAux]
  have : ¬ (n  < @Array.size α #[]) := n.not_lt_zero
  rw [dif_neg this]

theorem zipWith_nil_first (f : α → β → γ) (x : Array β) : Array.zipWith #[] x f = #[] := zipWithAux_nil_first f x 0 #[]

theorem zipWithAux_nil_second (f : α → β → γ) (x : Array α) (n : Nat) (z : Array γ) : Array.zipWithAux f x #[] n z = z := by
  rw [Array.zipWithAux]
  apply Decidable.byCases (p := n < x.size)
  case h1 =>
    intro hpos
    have : ¬(n < @Array.size β #[]) := n.not_lt_zero
    rw [dif_pos hpos, dif_neg this]
  case h2 =>
    intro hneg
    rw [dif_neg hneg]

theorem zipWith_nil_second (f : α → β → γ) (x : Array α) : Array.zipWith x #[] f = #[] := zipWithAux_nil_second f x 0 #[]

theorem zipWithAux_cons_cons_succ (f : α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) (n : Nat) (z : Array γ) : Array.zipWithAux f (Array.mk (a::as)) (Array.mk (b::bs)) (n+1) z = Array.zipWithAux f (Array.mk as) (Array.mk bs) n z := by
  rw [Array.zipWithAux]
  rw [Array.zipWithAux]
  apply Decidable.byCases (p:=n+1 < Array.size {data := a::as})
  case h1 =>
    intro hposa
    have hposa' : n < Array.size {data := as} := Nat.lt_of_succ_lt_succ hposa
    rw [dif_pos hposa, dif_pos hposa']
    apply Decidable.byCases (p:=n+1 < bs.length.succ)
    case h1 =>
      intro hposb
      have hposb' : n < bs.length := Nat.lt_of_succ_lt_succ hposb
      simp
      rw [dif_pos hposb, dif_pos hposb']; simp
      exact zipWithAux_cons_cons_succ f a as b bs n.succ _
    case h2 =>
      intro hnegb
      have hnegb' : ¬(n < bs.length) := fun h => hnegb (Nat.succ_lt_succ h)
      simp
      rw[dif_neg hnegb, dif_neg hnegb']
  case h2 =>
    intro hnega
    have hnega' : ¬(n < Array.size {data := as}) := fun h => hnega (Nat.succ_lt_succ h)
    rw [dif_neg hnega, dif_neg hnega']
termination_by _ => as.length - n

theorem zipWithAux_cons_cons_zero (f : α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) (z : Array γ) : Array.zipWithAux f {data := a::as} {data := b::bs} 0 z = Array.zipWithAux f {data := as} {data := bs} 0 (z.push (f a b)) := by
  rw [zipWithAux]
  have hsza : 0 < (Array.mk (a::as)).size := Nat.zero_lt_succ _
  have hszb : 0 < (Array.mk (b::bs)).size := Nat.zero_lt_succ _
  rw [dif_pos hsza, dif_pos hszb]
  simp
  rw [zipWithAux_cons_cons_succ]
  apply congrArg
  rfl

theorem zipWithAux_buf (f : α → β → γ) : ∀ (x : Array α) (y : Array β) (n : Nat) (z : Array γ), zipWithAux f x y n z = z ++ zipWithAux f x y n #[]
| Array.mk [], y, n => by
  intros z
  have : @Array.mk α [] = #[] := rfl
  rw [this, zipWithAux_nil_first, zipWithAux_nil_first]
  rw [Array.append_nil]
| Array.mk _, Array.mk [], n => by
  intros z
  have : @Array.mk β [] = #[] := rfl
  rw [this, zipWithAux_nil_second, zipWithAux_nil_second]
  rw [Array.append_nil]
| Array.mk (a::as), Array.mk (b::bs), 0 => by
  intros z
  rw [zipWithAux_cons_cons_zero, zipWithAux_cons_cons_zero]
  rw [zipWithAux_buf f {data := as} {data := bs} 0 (z.push (f a b))]
  rw [zipWithAux_buf f {data := as} {data := bs} 0 (#[].push (f a b))]
  rw [←append_assoc, append_push, append_nil]
| Array.mk (a::as), Array.mk (b::bs), (n+1) => by
  intros z
  rw [zipWithAux_cons_cons_succ, zipWithAux_cons_cons_succ]
  exact zipWithAux_buf f {data := as} {data := bs} n z

theorem zipWith_cons_cons (f : α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) : Array.zipWith {data := a::as} {data := b::bs} f = #[f a b] ++ (Array.zipWith {data := as} {data := bs} f) := by
  rw [zipWith, zipWith]
  rw [zipWithAux_buf, nil_append, zipWithAux_cons_cons_zero]
  rw [zipWithAux_buf, push_as_append, nil_append]

theorem zipWith_size (f : α → β → γ) : ∀ (x : Array α) (y : Array β), (Array.zipWith x y f).size = min x.size y.size
| Array.mk [], y => by
  conv =>
    lhs; change (zipWith #[] y f).size; rw [zipWith_nil_first]; change 0
  conv =>
    rhs; change min 0 y.size; rw [Nat.zero_min]
| x, Array.mk [] => by
  conv =>
    lhs; change (zipWith x #[] f).size; rw [zipWith_nil_second]; change 0
  conv =>
    rhs; change min x.size 0; rw [Nat.min_zero]
| Array.mk (a::as), Array.mk (b::bs) => by
  rw [zipWith_cons_cons, append_size]
  rw [size_cons, size_cons, Nat.min_succ_succ]
  have : size #[f a b] = 1 := rfl; rw [this]
  rw [zipWith_size f {data := as} {data := bs}]
  rw [Nat.add_comm]

end zipWith


/-!
## `Array.ofFn` in Std
-/

theorem ofFn_go_eq {α : Type u} {n : Nat} (f : Fin n → α) {i : Nat} {acc : Array α} : Array.ofFn.go f i acc = acc ++ Array.ofFn.go f i #[] := by
  by_cases i < n
  case pos hlt =>
    refine Nat.recAscend (motive:=λ i => ∀ acc, Array.ofFn.go f i acc = acc ++ Array.ofFn.go f i #[]) (n:=n) ?_ ?_ i (Nat.le_of_lt hlt) acc
    . dsimp; unfold Array.ofFn.go
      intro acc
      rw [dif_neg (Nat.lt_irrefl n), dif_neg (Nat.lt_irrefl n)]
      rfl
    . dsimp
      intro i hi h_ind acc
      unfold Array.ofFn.go
      rw [dif_pos hi, dif_pos hi]
      rw [h_ind (acc.push _), h_ind (#[].push _)]
      conv =>
        rhs; rw [←Array.append_assoc]
  case neg hnlt =>
    unfold Array.ofFn.go
    rw [dif_neg hnlt, dif_neg hnlt]
    rfl

theorem ofFn_go_succ {α : Type u} {n : Nat} (f : Fin n.succ → α) {i : Nat} {acc : Array α} : Array.ofFn.go f i.succ acc = Array.ofFn.go (f ∘ Fin.succ) i acc := by
  by_cases i < n
  case neg hnlt =>
    have : ¬ i.succ < n.succ := λ h => absurd (Nat.lt_of_succ_lt_succ h) hnlt
    unfold Array.ofFn.go
    rw [dif_neg this, dif_neg hnlt]
  case pos hlt =>
    refine Nat.recAscend (motive:=λ i =>∀ acc, Array.ofFn.go f i.succ acc = Array.ofFn.go (f ∘ Fin.succ) i acc) ?_ ?_ i (Nat.le_of_lt hlt) acc
      <;> dsimp
    . intro acc
      unfold Array.ofFn.go
      rw [dif_neg (Nat.lt_irrefl n.succ), dif_neg (Nat.lt_irrefl n)]
    . intro i hi h_ind acc
      unfold Array.ofFn.go
      rw [dif_pos (Nat.succ_lt_succ hi), dif_pos hi]
      rw [h_ind]
      rfl

theorem ofFn_succ {α : Type u} {n : Nat} (f : Fin n.succ → α) : (Array.ofFn f).data = f ⟨0,Nat.zero_lt_succ n⟩ :: (Array.ofFn (f ∘ Fin.succ)).data := by
  conv =>
    lhs; unfold Array.ofFn; unfold Array.ofFn.go
    rw [dif_pos n.zero_lt_succ]
    rw [Array.ofFn_go_succ, Array.ofFn_go_eq]
    rw [Array.append_data']

/-- `Classical`-free variant of `Array.getElem_ofFn` in Std -/
theorem getElem_ofFn' {α : Type u} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < (Array.ofFn f).size) : (Array.ofFn f)[i] = f ⟨i, Array.size_ofFn f ▸ h⟩ := by
  induction n generalizing i
  case zero =>
    exact absurd h (Nat.not_lt_zero i)
  case succ n h_ind =>
    rw [Array.getElem_eq_data_get]
    rw [List.get_congrList (Array.ofFn_succ f)]
    cases i
    case zero => rfl
    case succ i =>
      rw [List.get_cons_succ]
      rw [←Array.getElem_eq_data_get]
      rw [h_ind]
      rfl

/-- The symmetric counterpart of `getElem_ofFn'` -/
theorem getElem_ofFn'_symm {α : Type u} {n : Nat} (f : Fin n → α) (i : Fin n) : f i = (Array.ofFn f)[i.val]'((Array.size_ofFn f).symm ▸ i.isLt) :=
  Eq.symm $ getElem_ofFn' f i.val ((Array.size_ofFn f).symm ▸ i.isLt)

theorem foldl_ofFn_eq {α : Type u} {β : Type v} {init : β} {g : β → α → β} {n : Nat} {f : Fin n → α} : Array.foldl g init (Array.ofFn f) = Fin.foldAll (flip g ∘ f) init := by
  rw [Array.foldl_eq_foldl_data']
  induction n generalizing init
  case zero => rfl
  case succ n h_ind =>
    rw [ofFn_succ]; dsimp [List.foldl]; rw [h_ind, Fin.foldAll_succ]; rfl

#print axioms Array.foldl_ofFn_eq

end Array
