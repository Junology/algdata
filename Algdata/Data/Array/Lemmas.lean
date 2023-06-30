/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Basic
import Std.Data.Array.Lemmas

import Algdata.Init.Nat
import Algdata.Init.GetElem
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
## Declaration about `Array.cons`
-/

/--
An `Array` counterpart of `List.cons`.

:::note warning
In view of performance, construction based on `Array.push` is preferred.
:::
-/
def cons (a : α) (as : Array α) : Array α :=
  ⟨a :: as.data⟩

/-- Induction step for `Array` based on `Array.empty` (aka `#[]`) and `Array.cons`. -/
@[elab_as_elim]
theorem cons_induction {motive : Array α → Prop} (empty : motive #[]) (cons : ∀ (a : α) (x : Array α), motive x → motive (cons a x)) (x : Array α) : motive x :=
  x.rec $ List.rec empty λ a as IH => cons a ⟨as⟩ IH


/-!
## `Array.push` and `Array.pop`
-/

/-- `back' as h` is the last entry of `as : Array α` with `h : as.size > 0`. In contrast to `Array.back`, this function does not require `Inhabited α` since it doesn't fail thanks to `h`. -/
def back' (as : Array α) (h : as.size > 0) : α :=
  have : as.size - 1 < as.size := Nat.pred_lt' h
  as[as.size - 1]' this

/-- `Array.back'` is a counterpart of `List.getLast`. -/
theorem back'_eq_data_getLast (as : Array α) (h : as.size > 0) : as.back' h = as.data.getLast (h |> as.casesOn λ l (h : l.length > 0) (hc : l = []) => by cases hc; cases h) := by
  rw [List.getLast_eq_get]; rfl

/-- `Classical`-free version of `Array.get_push`-/
@[simp]
theorem get_push' (a : α) (as : Array α) (i : Nat) (h : i < (as.push a).size) : (as.push a)[i] = if h : i < as.size then as[i] else a := by
  cases as with | mk l =>
  simp only [getElem_eq_data_get]
  dsimp [push, size] at h ⊢
  rw [List.get_congrList (l.concat_eq_append a)]
  if hil : i < l.length
  then rw [dif_pos hil]; apply List.get_append_left
  else
    rw [dif_neg hil]
    have : i = l.length := by
      refine Nat.le_antisymm ?_ (Nat.ge_of_not_lt hil)
      rw [l.length_concat a] at h
      exact Nat.le_of_succ_le_succ h
    simp only [this]
    exact l.get_concat_length a _

/-- `as.pop[i] = as[i]` for `as : Array α` as long as the index `i` is valid. -/
@[simp]
theorem get_pop (as : Array α) (i : Nat) {hi₁ : i < as.pop.size} {hi₂ : i < as.size} : as.pop[i] = as[i] := by
  simp only [pop, getElem_eq_data_get, List.dropLast_eq_take]
  exact as.data.get_take _ i

/-- `Array.push`ing the last element, obtained by `Array.back'`, to the `Array.pop`ed array recovers the original array. -/
theorem push_pop_back' (as : Array α) (h : as.size > 0) : (as.pop).push (as.back' h) = as :=
  h |> as.casesOn λ l h => by
    simp only [back'_eq_data_getLast, pop, push, size, getElem_eq_data_get, List.concat_eq_append]
    apply congrArg Array.mk
    apply l.dropLast_concat_getLast

/-- Induction principle on `Array` based on `Array.push`. -/
@[elab_as_elim]
theorem push_induction {motive : Array α → Prop}
  (empty : motive #[])
  (push : ∀ (as : Array α) (a : α), motive as → motive (as.push a))
  : ∀ (as : Array α), motive as :=
  suffices ∀ (n : Nat) (as : Array α), as.size = n → motive as
  from λ as => this as.size as rfl
  Nat.rec (λ (mk []) _ => empty) λ n IH as hn => by
    rw [← as.push_pop_back' (hn ▸ n.zero_lt_succ)]
    apply push; apply IH
    calc as.pop.size
        = as.size - 1 := as.size_pop
      _ = n+1-1 := congrArg (·-1) hn


/-!
## `Array.size`
-/

@[simp]
theorem size_nil : @Array.size α #[] = 0 := rfl

@[simp]
theorem size_cons (a : α) (as : List α) : Array.size {data := a::as} = (Array.size {data := as}).succ := rfl

theorem size_eq_length_of_data (x : Array α) : x.size = x.data.length := rfl


/-!
## `Array.foldl`
-/

theorem foldlM_eq_foldlM_data'.aux [Monad m] (f : β → α → m β) (arr : Array α) (i j) (H : arr.size = i + j) (b) :
    foldlM.loop f arr arr.size (Nat.le_refl _) i j b = (arr.data.drop j).foldlM f b := by
  induction i generalizing j b with
  | zero =>
    simp only [Nat.zero_eq, Nat.zero_add] at H; cases H
    unfold foldlM.loop
    rw [dif_neg (Nat.lt_irrefl _), List.drop_length]
    rfl
  | succ i IH =>
    have IH := IH (j+1) $ H.trans $ Nat.succ_add i j
    have : j < arr.size := Nat.lt_of_add_succ_eq (Nat.add_comm .. ▸ H.symm)
    unfold foldlM.loop
    simp only [dif_pos this, bind_congr IH]
    conv => rhs; rw [← List.get_drop_eq_drop arr.data j this]

/-- `Classical`-free version of `Array.foldlM_eq_foldlM_data` in the standard library. -/
 theorem foldlM_eq_foldlM_data' [Monad m] (f : β → α → m β) (init : β) (arr : Array α) : arr.foldlM f init = arr.data.foldlM f init := by
  simp only [foldlM, Nat.le_refl, dif_pos, Nat.sub_zero]
  exact foldlM_eq_foldlM_data'.aux f arr arr.size 0 rfl init

/-- `Classical`-free version of `Array.foldl_eq_foldl_data` in the standard library. -/
theorem foldl_eq_foldl_data' (f : β → α → β) (init : β) (arr : Array α) : arr.foldl f init = arr.data.foldl f init :=
  arr.data.foldl_eq_foldlM f init ▸ arr.foldlM_eq_foldlM_data' (λ b a => pure (f b a)) init

theorem foldlM_cons {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (a : α) (as : Array α) : foldlM f init (.cons a as) = (f init a >>= λ b => foldlM f b as) :=
  match as with
  | mk l => by simp only [foldlM_eq_foldlM_data', cons]; rfl

/-- Induction step of `foldl` in terms of `Array.data`. -/
theorem foldl_cons {β : Type v} (f : β → α → β) (init : β) (a : α) (as : Array α) : foldl f init (.cons a as) = foldl f (f init a) as := by
  exact foldlM_cons (m:=Id) (λ b a => pure (f b a)) init a as

theorem foldlM_push {m : Type v → Type w} [Monad m] [LawfulMonad m] {β : Type v} (f : β → α → m β) (init : β) (as : Array α) (a : α) : foldlM f init (as.push a) = (foldlM f init as >>= λ b => f b a) := by
  simp only [foldlM_eq_foldlM_data', as.push_data a]
  conv => lhs; rw [List.foldlM_append]; rhs; ext; simp only [List.foldlM, bind_pure]

theorem foldl_push {β : Type v} (f : β → α → β) (init : β) (as : Array α) (a : α) : foldl f init (as.push a) = f (foldl f init as) a :=
  foldlM_push (m:=Id) f init as a

/-- In spite of the definition, `Array.foldlM` can be written in terms of `Array.foldl`. -/
theorem foldlM_eq_foldl {m : Type v → Type w} [Monad m] [LawfulMonad m] {β : Type v} (f : β → α → m β) (init : β) (x : Array α) : foldlM f init x = foldl (λ (z : m β) a => z >>= λ b => f b a) (pure init) x :=
  x.push_induction rfl λ a x IH => by
    rw [foldlM_push, foldl_push, IH]


/-!
## `Array.map`
-/

section Map

variable {m : Type v → Type w} [Monad m]

theorem mapM_empty (f : α → m β) : mapM f #[] = pure #[] :=
  rfl

theorem mapM.map_cons_succ [LawfulMonad m] (f : α → m β) (a : α) (x : Array α) (i : Nat) (b : β) (y : Array β) : Array.mapM.map f (cons a x) (i+1) (cons b y) = (Array.mapM.map f x i y >>= λ y => pure (cons b y)) := by
  unfold map; dsimp [cons]
  if h : i < x.size then
    rw [dif_pos (Nat.succ_lt_succ h), dif_pos h, bind_assoc]
    apply bind_congr; intro b'
    exact mapM.map_cons_succ f a x (i+1) b (push y b')
  else
    rw [dif_neg h, dif_neg (h ∘ Nat.lt_of_succ_lt_succ)]
    rw [pure_bind]
termination_by _ => x.size-i

theorem mapM_cons [LawfulMonad m] (f : α → m β) (a : α) (x : Array α) : mapM f (cons a x) = (f a >>= λ b => mapM f x >>= λ y => pure (cons b y)) := by
  unfold mapM
  conv =>
    lhs; unfold mapM.map; dsimp [cons]
    rw [dif_pos x.size.zero_lt_succ]
  apply bind_congr; intro b
  exact mapM.map_cons_succ f a x 0 b #[]

theorem mapM_push [LawfulMonad m] (f : α → m β) (x : Array α) (a : α) : mapM f (x.push a) = (x.mapM f >>= λ y => f a >>= λ b => pure (y.push b)) :=
  x.cons_induction
    (Eq.trans (mapM_cons f a #[]) $ by simp only [mapM_empty, pure_bind]; rfl)
    λ a x IH => by
      show mapM f (cons a (push x _)) = _
      simp only [mapM_cons f, bind_assoc]
      apply bind_congr; intro b
      rw [IH]; simp only [bind_assoc, pure_bind]; rfl

theorem map_push (f : α → β) (x : Array α) (a : α) : map f (x.push a) = (x.map f).push (f a) :=
  mapM_push (m:=Id) f x a

/-- `Classical`-free version of `Array.map_data`. -/
theorem map_data' (f : α → β) (arr : Array α) : (arr.map f).data = List.map f arr.data :=
  arr.push_induction rfl λ x a IH => by
    simp only [map_push, push_data, IH, List.map_append]; rfl

theorem map_cons (f : α → β) (a : α) (x : Array α) : map f (.cons a x) = .cons (f a) (map f x) :=
  ext' $ by simp only [map_data', cons]; rfl

/-- `Classical`-free version of `Array.size_mapM`. -/
theorem size_mapM' [LawfulMonad m] (f : α → m β) (x : Array α) : SatisfiesM (λ y => y.size = x.size) (x.mapM f) :=
  x.push_induction
    ⟨pure ⟨#[],rfl⟩, by rw [map_pure]; rfl⟩
    λ x a ⟨y,h⟩ =>
      let push' : {y : Array β // y.size = x.size} → (b : β) → {y : Array β // y.size = (x.push a).size} :=
        λ y b => ⟨y.1.push b, y.1.size_push b ▸ x.size_push a ▸ congrArg (·+1) y.2⟩
      Exists.intro (y >>= λ y => push' y <$> f a) $ by
        rw [mapM_push, ← h]
        simp only [map_eq_pure_bind, bind_assoc]
        apply bind_congr; intro y
        simp only [pure_bind]

/-- `Classical`-free version of `Array.size_map`. -/
theorem size_map' (f : α → β) (arr : Array α) : (arr.map f).size = arr.size :=
  calc (arr.map f).size
      = (arr.map f).data.length := rfl
    _ = (List.map f arr.data).length := congrArg _ (arr.map_data' f)
    _ = arr.data.length := arr.data.length_map f
    _ = arr.size := rfl

/-- `Classical`-free version of `Array.getElem_map`. -/
theorem getElem_map' (f : α → β) (arr : Array α) (i : Nat) (hi : i < (arr.map f).size) : (arr.map f)[i] = f (arr[i]'(arr.size_map' f ▸ hi)) := by
  show (arr.map f).data[i] = f (arr[i]' _)
  rw [getElem_eq (arr.map_data' f) (Eq.refl i)]
  exact List.get_map f

theorem mapIdxM_empty (f : Fin 0 → α → m β) : mapIdxM #[] f = pure #[] :=
  rfl

theorem mapIdxM.map_cons (a : α) (x : Array α) (f : Fin (x.size +1) → α → m β) (i j : Nat) (h : i + (j+1) = x.size + 1) (y : Array β) : mapIdxM.map (cons a x) f i (j+1) h y = (mapIdxM.map x (f ∘ Fin.succ) i j (Nat.succ.inj h) y) := by
  induction i generalizing j y with
  | zero => dsimp [map]
  | succ i IH =>
    unfold map; dsimp
    apply bind_congr; intro b
    exact IH (j+1) _ (push y b)

theorem mapIdxM_cons [LawfulMonad m] (a : α) (x : Array α) (f : Fin (x.size + 1) → α → m β) : mapIdxM (cons a x) f = (f ⟨0,x.size.zero_lt_succ⟩ a >>= λ b => mapIdxM x (f ∘ Fin.succ) >>= λ y => pure (cons b y)) := by
  unfold mapIdxM
  conv => lhs; unfold mapIdxM.map; dsimp [cons]
  apply bind_congr; intro b
  show mapIdxM.map (cons a x) f x.size 1 rfl #[b] = _
  rw [mapIdxM.map_cons]
  generalize f ∘ Fin.succ = f'; clear f
  suffices ∀ (i j) (h : i + j = x.size) (y : Array β), mapIdxM.map x f' i j h (cons b y) = (mapIdxM.map x f' i j h y >>= λ y => pure (cons b y))
  from this x.size 0 rfl #[]
  intro i j h y
  induction i generalizing j y with
  | zero => dsimp [mapIdxM.map]; rw [pure_bind]
  | succ i IH =>
    dsimp [mapIdxM.map]; simp only [bind_assoc]
    apply bind_congr; intro b'
    dsimp [push, cons, List.concat]
    exact IH ..

theorem mapIdx_empty (f : Fin 0 → α → β) : mapIdx #[] f = #[] :=
  rfl

theorem mapIdx_cons (a : α) (x : Array α) (f : Fin (x.size + 1) → α → β) : mapIdx (cons a x) f = cons (f ⟨0,x.size.zero_lt_succ⟩ a) (mapIdx x (f ∘ Fin.succ)) :=
  mapIdxM_cons (m:=Id) a x f

theorem size_mapIdx' (x : Array α) (f : Fin x.size → α → β) : (mapIdx x f).size = x.size :=
  f |> x.cons_induction (λ _ => rfl) λ a x IH f => by
    rw [mapIdx_cons]; dsimp [cons]
    exact congrArg Nat.succ (IH (f ∘ Fin.succ))

end Map


/-!
## `Array.append`
-/

theorem append_nil (x : Array α) : x ++ #[] = x :=
  rfl

theorem append_push (x y : Array α) (a : α) : x ++ (y.push a) = (x ++ y).push a :=
  -- Recall `Array.append = Array.foldl Array.push`
  foldl_push Array.push x y a

/-- `Classical`-free analogue of `append_data` in Std4. -/
theorem append_data' (x y : Array α) : (x ++ y).data = x.data ++ y.data := by
  show (Array.append x y).data = x.data ++ y.data
  unfold Array.append; rw [foldl_eq_foldl_data']
  rw [← y.data.foldl_hom Array.data Array.push (λ l a => l ++ [a]) x λ arr a => (arr.push_data a).symm]
  generalize x.data = l; generalize y.data = l'
  induction l' generalizing l with
  | nil => exact Eq.symm $ l.append_nil
  | cons b bs IH =>
    unfold List.foldl; rw [IH]; exact Eq.symm $ l.append_cons b bs

theorem nil_append (x : Array α) : #[] ++ x = x :=
  x.push_induction rfl λ x a IH =>
    calc #[] ++ (x.push a)
        = (#[] ++ x).push a := append_push #[] x a
      _ = x.push a := congrArg (λ x => push x a) IH

theorem append_assoc (x y z : Array α) : (x ++ y) ++ z = x ++ (y ++ z) :=
  z.push_induction rfl λ z c IH => by
    simp only [append_push]
    exact congrArg (push · c) IH

theorem push_as_append (x : Array α) (a : α) : x.push a = x ++ #[a] :=
  rfl

theorem size_append (x y : Array α) : (x ++ y).size = x.size + y.size := by
  dsimp [size]; rw [append_data' x y]; exact List.length_append x.data y.data


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


/-!
## `Array.zipWith`
-/

section zipWith

variable {β : Type v} {γ : Type w}

theorem zipWithAux_nil_first (f : α → β → γ) (x : Array β) (n : Nat) (z : Array γ) : Array.zipWithAux f #[] x n z = z := by
  unfold Array.zipWithAux; exact dif_neg n.not_lt_zero

theorem zipWith_nil_first (f : α → β → γ) (x : Array β) : Array.zipWith #[] x f = #[] :=
  zipWithAux_nil_first f x 0 #[]

theorem zipWithAux_nil_second (f : α → β → γ) (x : Array α) (n : Nat) (z : Array γ) : Array.zipWithAux f x #[] n z = z := by
  unfold Array.zipWithAux; dsimp [size]; simp only [dif_neg n.not_lt_zero]
  apply dite (n < x.size) <;> (intro h; simp only [h, dif_neg, dif_pos])

theorem zipWith_nil_second (f : α → β → γ) (x : Array α) : Array.zipWith x #[] f = #[] :=
  zipWithAux_nil_second f x 0 #[]

theorem zipWithAux_cons_cons_succ (f : α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) (n : Nat) (z : Array γ) : Array.zipWithAux f (Array.mk (a::as)) (Array.mk (b::bs)) (n+1) z = Array.zipWithAux f (Array.mk as) (Array.mk bs) n z := by
  unfold zipWithAux
  refine dite_congr (propext ⟨Nat.lt_of_succ_lt_succ,Nat.succ_lt_succ⟩) ?_ (λ _ => rfl)
  intros
  refine dite_congr (propext ⟨Nat.lt_of_succ_lt_succ,Nat.succ_lt_succ⟩) ?_ (λ _ => rfl)
  intros; dsimp
  exact zipWithAux_cons_cons_succ f a as b bs (n+1) _
termination_by _ => as.length - n

theorem zipWithAux_cons_cons_zero (f : α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) (z : Array γ) : Array.zipWithAux f {data := a::as} {data := b::bs} 0 z = Array.zipWithAux f {data := as} {data := bs} 0 (z.push (f a b)) := by
  conv =>
    lhs
    unfold zipWithAux; dsimp
    rw [dif_pos as.length.zero_lt_succ, dif_pos bs.length.zero_lt_succ]
    rw [zipWithAux_cons_cons_succ]

theorem zipWithAux_data_eq_zipWithTR_go (f : α → β → γ) (x : Array α) (y : Array β) (z : Array γ) : (zipWithAux f x y 0 z).data = List.zipWithTR.go f x.data y.data z := by
  cases x with | mk l =>
  cases y with | mk l' =>
  dsimp
  induction l generalizing l' z with
  | nil => exact (congrArg data (zipWithAux_nil_first f _ 0 z)).trans z.toList_eq.symm
  | cons a l IH =>
    cases l' with
    | nil => exact (congrArg data (zipWithAux_nil_second f _ 0 z)).trans z.toList_eq.symm
    | cons => rw [zipWithAux_cons_cons_zero]; exact IH _ _

theorem zipWith_data_eq_zipWith_data (f : α → β → γ) (x : Array α) (y : Array β) : (zipWith x y f).data = List.zipWith f x.data y.data := by
  show (zipWithAux f x y 0 #[]).data = List.zipWith f x.data y.data
  rw [zipWithAux_data_eq_zipWithTR_go, List.zipWith_eq_zipWithTR]
  rfl

theorem size_zipWith (f : α → β → γ) (x : Array α) (y : Array β) : (Array.zipWith x y f).size = min x.size y.size := by
  simp only [size, zipWith_data_eq_zipWith_data]
  exact List.length_zipWith' f x.data y.data

end zipWith


section ModifyM

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u}

theorem size_modifyM (x : Array α) (n : Nat) (f : α → m α) : SatisfiesM (fun y => y.size = x.size) (x.modifyM n f) := by
  unfold modifyM
  if h : n < x.size
  then
    rw [dif_pos h]; dsimp
    exists (f x[n] >>= λ v => pure ⟨x.set ⟨n,h⟩ v, x.size_set ⟨n,h⟩ v⟩)
    rw [map_eq_pure_bind, bind_assoc]
    apply bind_congr; intro a
    exact pure_bind ..
  else rw [dif_neg h]; exact ⟨pure ⟨x,rfl⟩, map_pure Subtype.val _⟩

@[simp]
theorem size_modify : ∀ (x : Array α) (n : Nat) (f : α → α), (x.modify n f).size = x.size := by
  intro x n f
  cases size_modifyM (m:=Id) x n f with | intro w hw =>
  dsimp at hw
  conv at hw => rhs; change modify x n f
  rw [←hw]
  exact w.property

end ModifyM


/-!
## `Array.ofFn` in Std
-/

theorem ofFn_go_zero (f : Fin 0 → α) (i : Nat) (acc : Array α) : ofFn.go f i acc = acc := by
  unfold ofFn.go; exact dif_neg i.not_lt_zero

theorem ofFn_go_succ {n : Nat} (f : Fin (n+1) → α) (i : Nat) (acc : Array α) (H : i < n+1) : Array.ofFn.go f i acc = (Array.ofFn.go (λ (x : Fin n) => f ⟨x.1, Nat.lt_succ_of_lt x.2⟩) i acc).push (f ⟨n,n.lt_succ_self⟩) :=
  Or.elim (Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ H))
    (λ (h : i < n) => by
      unfold ofFn.go; rw [dif_pos H, dif_pos h]
      exact ofFn_go_succ f (i+1) _ (Nat.succ_lt_succ h)
    )
    (λ (h : i = n) => by
      cases h
      unfold ofFn.go; rw [dif_pos n.lt_succ_self]
      unfold ofFn.go; rw [dif_neg (n+1).lt_irrefl]
      unfold ofFn.go; rw [dif_neg n.lt_irrefl]
    )
termination_by _ => n-i

theorem ofFn_zero (f : Fin 0 → α) : ofFn f = #[] :=
  rfl

theorem ofFn_succ {n : Nat} (f : Fin (n+1) → α) : ofFn f = (ofFn (λ x => f ⟨x.1,Nat.lt_succ_of_lt x.2⟩)).push (f ⟨n,n.lt_succ_self⟩) :=
  ofFn_go_succ f 0 (mkEmpty (n+1)) n.zero_lt_succ

/-- `Classical`-free variant of `Array.getElem_ofFn` in Std -/
theorem getElem_ofFn' {n : Nat} (f : Fin n → α) (i : Nat) : (h : i < size (ofFn f)) → (ofFn f)[i] = f ⟨i, size_ofFn f ▸ h⟩ :=
  f |> n.rec (λ _ h => have := size_ofFn f ▸ h; nomatch this) λ n IH f h => by
    simp only [ofFn_succ f, get_push']
    if h' : i < size (ofFn λ x => f ⟨x.1, Nat.lt_succ_of_lt x.2⟩)
    then rw [dif_pos h']; exact IH _ h'
    else
      rw [dif_neg h']
      suffices i = n by cases this; rfl
      simp only [size_ofFn] at h h'
      exact Nat.le_antisymm (Nat.le_of_succ_le_succ h) (Nat.ge_of_not_lt h')

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

theorem ofFn_go_succ' {α : Type u} {n : Nat} (f : Fin n.succ → α) {i : Nat} {acc : Array α} : Array.ofFn.go f i.succ acc = Array.ofFn.go (f ∘ Fin.succ) i acc := by
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

theorem ofFn_succ' {α : Type u} {n : Nat} (f : Fin n.succ → α) : (Array.ofFn f).data = f ⟨0,Nat.zero_lt_succ n⟩ :: (Array.ofFn (f ∘ Fin.succ)).data := by
  conv =>
    lhs; unfold Array.ofFn; unfold Array.ofFn.go
    rw [dif_pos n.zero_lt_succ]
    rw [Array.ofFn_go_succ', Array.ofFn_go_eq]
    rw [Array.append_data']

/-- The symmetric counterpart of `getElem_ofFn'` -/
theorem getElem_ofFn'_symm {α : Type u} {n : Nat} (f : Fin n → α) (i : Fin n) : f i = (Array.ofFn f)[i.val]'((Array.size_ofFn f).symm ▸ i.isLt) :=
  Eq.symm $ getElem_ofFn' f i.val ((Array.size_ofFn f).symm ▸ i.isLt)

theorem foldl_ofFn_eq {α : Type u} {β : Type v} {init : β} {g : β → α → β} {n : Nat} {f : Fin n → α} : Array.foldl g init (Array.ofFn f) = Fin.foldAll (flip g ∘ f) init := by
  rw [Array.foldl_eq_foldl_data']
  induction n generalizing init
  case zero => rfl
  case succ n h_ind =>
    rw [ofFn_succ']; dsimp [List.foldl]; rw [h_ind, Fin.foldAll_succ]; rfl

end Array
