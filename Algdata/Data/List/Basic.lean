/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas

import Algdata.Tactic.PkgLocal

import Algdata.Init.Fin
import Algdata.Init.LawfulLT

pkg_include Nat.min_zero', min_succ_succ'

/-!
# Auxiliary declaration about `List`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

namespace List

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}


/-! ### Lemmas about the functions in the core library -/
@[pkg_local]
private theorem get_congr {x y : List α} {i : Fin x.length} {j : Fin y.length} : x = y → i.val = j.val → get x i = get y j
| rfl, h => by rw [Fin.eq_of_val_eq h]

@[pkg_local]
private theorem get_proof_irrev (x : List α) (i : Fin x.length) (h : i.val < x.length) : x.get i = x.get ⟨i.val, h⟩ :=
  get_congr rfl rfl

@[pkg_local]
private theorem get_concat_length (l : List α) (a : α) (h : l.length < (l ++ [a]).length) : get (l ++ [a]) ⟨l.length, h⟩ = a := by
  apply Option.some.inj
  rw [←get?_eq_get, get?_concat_length]

@[pkg_local]
private theorem get_take (l : List α) (n : Nat) (i : Nat) {hi₁ : i < (l.take n).length} {hi₂ : i < l.length} : get (l.take n) ⟨i,hi₁⟩ = get l ⟨i,hi₂⟩ := by
  rw [get_of_eq (l.take_append_drop n).symm, get_append_left]

@[pkg_local]
private theorem dropLast_eq_take (as : List α) : as.dropLast = as.take (as.length - 1) :=
  as.rec rfl fun
  | _, [], _ => rfl
  | a, (_ :: _), IH => congrArg (a :: ·) IH

@[pkg_local]
private theorem singleton_getLast_eq_drop (as : List α) (h : as ≠ []) : [as.getLast h] = as.drop (as.length - 1) :=
  h |> as.rec (λ h => nomatch h) λ a as IH _ =>
    show [(a::as).getLast (λ h => nomatch h)] = drop (length as) (a :: as)
    from IH |> as.casesOn (λ _ => rfl) λ _ _ IH => IH λ h => nomatch h

@[pkg_local]
private theorem dropLast_concat_getLast (as : List α) (h : as ≠ []) : as.dropLast ++ [as.getLast h] = as := by
  rw [as.dropLast_eq_take, as.singleton_getLast_eq_drop]
  exact as.take_append_drop (as.length - 1)

@[pkg_local]
private theorem dropLast_concat_getLast' (as : List α) (h : as ≠ []) : as.dropLast.concat (as.getLast h) = as := by
  rw [List.concat_eq_append]; exact as.dropLast_concat_getLast h

@[pkg_local]
private theorem zipWith_nil_first (f : α → β → γ) : ∀ (x : List β), List.zipWith f [] x = []
| [] => rfl
| (_::_) => rfl

@[pkg_local]
private theorem zipWith_nil_second (f : α → β → γ) : ∀ (x : List α), List.zipWith f x [] = []
| [] => rfl
| (_::_) => rfl

/-- `Classical`-free version of `List.length_zipWith` in Std library -/
@[pkg_local]
private theorem length_zipWith' (f : α → β → γ) (l₁ : List α) (l₂ : List β) : length (zipWith f l₁ l₂) = min l₁.length l₂.length :=
  l₂ |> l₁.rec
    (λ l₂ => l₂.zipWith_nil_first f ▸ l₂.length.zero_min.symm)
    λ a l₁ IH => fun
      | [] => (a::l₁).zipWith_nil_second f ▸ (a::l₁).length.min_zero'.symm
      | _::l₂ => (congrArg (·+1) (IH l₂)).trans (Nat.min_succ_succ' _ _).symm

@[pkg_local]
private theorem reverseAux_append_left {as₁ as₂ bs : List α} : reverseAux (as₁ ++ as₂) bs = as₂.reverse ++ reverseAux as₁ bs := by
  revert bs; induction as₁ <;> intro bs
  case nil => rw [reverseAux_eq_append]; rfl
  case cons a₁ as₁ h_ind =>
    rw [cons_append]
    unfold reverseAux
    rw [h_ind]

@[pkg_local]
private theorem bind_congr : ∀ {as₁ as₂ : List α} {f₁ f₂ : α → List β}, as₁ = as₂ → (∀ a, f₁ a = f₂ a) → as₁.bind f₁ = as₂.bind f₂
| as, _, _, _, rfl, h =>
  congrArg (as.bind) (funext h)

@[pkg_local]
private theorem bind_map_binary_eq_map_bind_map (f : α → β → γ) (as : List α) (bs : List β) : as.bind (fun a => bs.map (f a)) = (as.map f).bind bs.map := by
  induction as with
  | nil => rfl
  | cons a as hi =>
    rw [cons_bind, map, cons_bind]
    rw [hi]


/-! ### Variant of `mapIdx` -/

/-- A variant of `List.mapIdx`; the version uses mapping with indices of type `Fin l.length` instead of `Nat`. -/
@[inline]
def mapIdx' (as : List α) (f : Fin as.length → α → β) : List β :=
  go as #[] rfl where
    /-- Auxiliary for `mapIdx`:
    `mapIdx.go [a₀, a₁, ...] acc = acc.toList ++ [f acc.size a₀, f (acc.size + 1) a₁, ...]` -/
    @[specialize] go : (l : List α) → (acc : Array β) → l.length + acc.size = as.length → List β
    | [], acc, _ => acc.toList
    | a :: tl, acc, h =>
      have : acc.size < as.length :=
        calc acc.size
          _ < (tl.length + 1) + acc.size := Nat.lt_add_of_pos_left tl.length.zero_lt_succ
          _ = as.length := h
      go tl (acc.push (f ⟨acc.size, this⟩ a)) $ by
        rw [Array.size_push, ← h, length_cons, Nat.succ_add]
        rfl

theorem mapIdx'_nil (f : Fin 0 → α → β) : mapIdx' [] f = [] :=
  rfl

theorem mapIdx'_cons (a : α) (as : List α) (f : Fin (as.length + 1) → α → β) : mapIdx' (a :: as) f = f ⟨0, as.length.zero_lt_succ⟩ a :: mapIdx' as (f ∘ Fin.succ) := by
  suffices ∀ (l : List α) (b : β) (acc : Array β) (h : l.length + (acc.size + 1) = as.length + 1), mapIdx'.go (a :: as) f l ⟨b :: acc.data⟩ h = b :: mapIdx'.go as (f ∘ Fin.succ) l acc (Nat.succ.inj h)
  by
    dsimp [mapIdx', mapIdx'.go, Array.push, concat]
    exact this as _ #[] _
  intros l b acc h
  induction l generalizing acc with
  | nil => dsimp [mapIdx'.go]; simp only [Array.toList_eq]
  | cons a' tl IH =>
    dsimp [mapIdx'.go, Array.push, concat]
    exact IH (acc.push (f _ a')) _

theorem length_mapIdx' (as : List α) (f : Fin as.length → α → β) : (as.mapIdx' f).length = as.length :=
  f |> as.rec (fun _ => rfl) fun a as IH f => by
    simp only [mapIdx'_cons, length, IH]

theorem getElem_mapIdx'
    (as : List α) (f : Fin as.length → α → β) (i : Nat) (hi : i < (as.mapIdx' f).length)
  : (as.mapIdx' f)[i]'hi = f ⟨i, as.length_mapIdx' f ▸ hi⟩ (as[i]'(as.length_mapIdx' f ▸ hi)) := by
  induction as generalizing i with
  | nil => cases hi
  | cons a as IH =>
    simp only [mapIdx'_cons]
    cases i with
    | zero => rfl
    | succ i => simp only [cons_getElem_succ, IH]; rfl


/-! ### Lexicographical strict order on `List` -/

--- Lexicographical lift of relations
protected
inductive lex (r : α → α → Prop) : List α → List α → Prop
| nil : (a : α) → (as : List α) → List.lex r [] (a::as)
| head {a b : α} {as bs : List α} : r a b → List.lex r (a::as) (b::bs)
| tail {a : α} {as bs : List α} : List.lex r as bs → List.lex r (a::as) (a::bs)

namespace lex

variable {r : α → α → Prop}

protected
theorem trans [Trans r r r] : {as bs cs : List α} → List.lex r as bs → List.lex r bs cs → List.lex r as cs
| [], (_::_), (_::_), List.lex.nil _ _, List.lex.head _ => List.lex.nil _ _
| [], (_::_), (_::_), List.lex.nil _ _, List.lex.tail _ => List.lex.nil _ _
| (_::_), (_::_), (_::_), List.lex.head hab, List.lex.head hbc => List.lex.head (trans hab hbc)
| (_::_), (_::_), (_::_), List.lex.head hab, List.lex.tail _ => List.lex.head hab
| (_::_), (_::_), (_::_), List.lex.tail _, List.lex.head hbc => List.lex.head hbc
| (_::_), (_::_), (_::_), List.lex.tail hab, List.lex.tail hbc => List.lex.tail (List.lex.trans hab hbc)

protected
theorem irrefl [Irreflective r] : ∀ (as : List α), ¬ List.lex r as as
| (_::_), List.lex.head h => absurd h (Irreflective.irrefl _)
| (_::_), List.lex.tail h => List.lex.irrefl _ h

protected
theorem asymm [Asymmetry r] : ∀ (as bs : List α), List.lex r as bs → ¬ List.lex r bs as
| (_::_), (_::_), List.lex.head hab, List.lex.head hba =>
  Asymmetry.asymm _ _ hab hba
| (_::_), (_::_), List.lex.head hab, List.lex.tail _ =>
  Asymmetry.asymm _ _ hab hab
| (_::_), (_::_), List.lex.tail _, List.lex.head hba =>
  Asymmetry.asymm _ _ hba hba
| (_::_), (_::_), List.lex.tail hab, List.lex.tail hba =>
  List.lex.asymm _ _ hab hba

protected
theorem trichot [Trichotomous r] : ∀ (as bs : List α), as = bs ∨ List.lex r as bs ∨ List.lex r bs as
| [], [] => Or.inl rfl
| [], (_::_) => Or.inr $ Or.inl $ List.lex.nil _ _
| (_::_), [] => Or.inr $ Or.inr $ List.lex.nil _ _
| (a::as), (b::bs) =>
  trichot_cases_on r a b
    (λ a h_ind =>
      Or.imp (congrArg (List.cons a)) (Or.imp List.lex.tail List.lex.tail) h_ind
    )
    (λ _ _ h _ => Or.inr $ Or.inl $ List.lex.head h)
    (λ _ _ h _ => Or.inr $ Or.inr $ List.lex.head h)
    (List.lex.trichot as bs)

instance instTransListLex [Trans r r r] : Trans (List.lex r) (List.lex r) (List.lex r) where
  trans := List.lex.trans

instance instIrreflectiveListLex [Irreflective r] : Irreflective (List.lex r) where
  irrefl := List.lex.irrefl

instance instAsymmetryListLex [Asymmetry r] : Asymmetry (List.lex r) where
  asymm := List.lex.asymm

instance instTrichotomousListLex [Trichotomous r] : Trichotomous (List.lex r) where
  trichot := List.lex.trichot

instance instDecidableRelListLex [DecidableEq α] [DecidableRel r] : DecidableRel (List.lex r)
| [], [] => isFalse $ λ hcontra => by cases hcontra
| (a::as), [] => isFalse $ λ hcontra => by cases hcontra
| [], (b::bs) => isTrue $ List.lex.nil _ _
| (a::as), (b::bs) =>
  if hab : r a b then
    isTrue $ List.lex.head hab
  else if heq : a = b then
    match instDecidableRelListLex as bs with
    | isTrue htail => isTrue $ heq ▸ List.lex.tail htail
    | isFalse htail => isFalse $ by
      cases heq; intro hcontra; cases hcontra <;> contradiction
  else
    isFalse $ λ hcontra => by
      cases hcontra <;> contradiction

end lex

end List
