/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas

import Algdata.Init.Fin
import Algdata.Init.LawfulLT

namespace List

universe u
variable {α : Type u}

theorem get_congr {x y : List α} {i : Fin x.length} {j : Fin y.length} : x = y → i.val = j.val → get x i = get y j
| rfl, h => by rw [Fin.eq_of_val_eq h]

theorem get_congrList {x y : List α} {i : Fin x.length} : (h : x = y) → get x i = get y ⟨i.val, h▸i.isLt⟩
| rfl => rfl

theorem get_proof_irrev (x : List α) (i : Fin x.length) (h : i.val < x.length) : x.get i = x.get ⟨i.val, h⟩ :=
  get_congr rfl rfl

theorem get_head (a : α) (as : List α) : ∀ {i : Fin (as.length + 1)}, i = 0 → (a::as).get i = a
| _, rfl => rfl

theorem get_tail (a : α) (as : List α) : ∀ {i : Fin (as.length + 1)} (hi : i ≠ 0), (a::as).get i = as.get (i.pred hi)
| Fin.mk 0 _, hpos => nomatch hpos
| Fin.mk (_+1) _, _ => rfl

theorem get_concat_length (l : List α) (a : α) (h : l.length < (l ++ [a]).length) : get (l ++ [a]) ⟨l.length, h⟩ = a := by
  apply Option.some.inj
  rw [←get?_eq_get, get?_concat_length]

theorem get_set_on : ∀ (x : List α) (i : Nat) (v : α) (j : Fin (x.set i v).length), i = j.val → get (x.set i v) j = v
| [], _, _, Fin.mk _ hk, _ => (Nat.not_lt_zero _ hk).elim
| (a::as), 0, v, Fin.mk 0 _, _ => rfl
| (a::as), 0, v, Fin.mk (k+1) hk, h => (Nat.succ_ne_zero _ h.symm).elim
| (a::as), (i+1), v, Fin.mk 0 _, h => (Nat.succ_ne_zero _ h).elim
| (a::as), (i+1), v, Fin.mk (k+1) hk, h => by
  have hset : set (a::as) i.succ v = a::(as.set i v) := rfl
  rw [get_congr hset rfl, get]
  rw [get_set_on as]
  exact Nat.succ.inj h

theorem get_set_off : ∀ (x : List α) (i : Nat) (v : α) (j : Fin (x.set i v).length), i ≠ j.val → get (x.set i v) j = get x ⟨j.val, x.length_set i v ▸ j.isLt⟩
| [], _, _, Fin.mk _ hk, _ => (Nat.not_lt_zero _ hk).elim
| (a::as), 0, v, Fin.mk 0 _, h => (h rfl).elim
| (a::as), 0, v, Fin.mk (k+1) hk, _ => by
  have : set (a::as) 0 v = v::as := rfl
  rw [get_congr this rfl, get, get]
| (a::as), (i+1), v, Fin.mk 0 _, _ => by
  have : set (a::as) (i+1) v = a :: set as i v := rfl
  rw [get_congr this rfl, get, get]
| (a::as), (i+1), v, Fin.mk (k+1) hk, h => by
  have : set (a::as) (i+1) v = a :: set as i v := rfl
  rw [get_congr this rfl, get, get]
  rw [get_set_off as i v ⟨k,_⟩ (h ∘ congrArg Nat.succ)]

theorem get_take (l : List α) (n : Nat) (i : Nat) {hi₁ : i < (l.take n).length} {hi₂ : i < l.length} : get (l.take n) ⟨i,hi₁⟩ = get l ⟨i,hi₂⟩ := by
  rw [get_congrList (l.take_append_drop n).symm, get_append_left]

theorem foldl_comm {α β : Type _} {f : α → β → α} {g : α → α} : (∀ a b, f (g a) b = g (f a b)) → ∀ {init : α} {bs : List β}, bs.foldl f (g init) = g (bs.foldl f init) := by
  intro hfg init bs
  revert init; induction bs
  case nil => exact λ {_} => rfl
  case cons b bs h_ind =>
    intro init
    dsimp [foldl]
    rw [hfg init b, h_ind (init:=f init b)]

theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) : ∀ (as : List α), as.map (g ∘ f) = (as.map f).map g
| [] => rfl
| (a::as) => by unfold map; rw [comp_map f g as]; rfl

theorem comp_filterMap {α β γ : Type _} (f : α → β) (g : β → Option γ) : ∀ (as : List α), as.filterMap (g ∘ f) = (as.map f).filterMap g
| [] => rfl
| (a::as) => by
  unfold map; unfold filterMap
  rw [comp_filterMap f g as]
  rfl

theorem dropLast_eq_take (as : List α) : as.dropLast = as.take (as.length - 1) :=
  as.rec rfl fun
  | _, [], _ => rfl
  | a, (_ :: _), IH => congrArg (a :: ·) IH

theorem singleton_getLast_eq_drop (as : List α) (h : as ≠ []) : [as.getLast h] = as.drop (as.length - 1) :=
  h |> as.rec (λ h => nomatch h) λ a as IH _ =>
    show [(a::as).getLast (λ h => nomatch h)] = drop (length as) (a :: as)
    from IH |> as.casesOn (λ _ => rfl) λ _ _ IH => IH λ h => nomatch h

#print axioms singleton_getLast_eq_drop

@[simp]
theorem dropLast_concat_getLast (as : List α) (h : as ≠ []) : as.dropLast ++ [as.getLast h] = as := by
  rw [as.dropLast_eq_take, as.singleton_getLast_eq_drop]
  exact as.take_append_drop (as.length - 1)

#print axioms dropLast_concat_getLast

@[simp]
theorem dropLast_concat_getLast' (as : List α) (h : as ≠ []) : as.dropLast.concat (as.getLast h) = as := by
  rw [List.concat_eq_append]; exact as.dropLast_concat_getLast h

theorem zipWith_nil_first {β γ : Type _} (f : α → β → γ) : ∀ (x : List β), List.zipWith f [] x = []
| [] => rfl
| (_::_) => rfl

theorem zipWith_nil_second {β γ : Type _} (f : α → β → γ) : ∀ (x : List α), List.zipWith f x [] = []
| [] => rfl
| (_::_) => rfl

/-- `Classical`-free version of `List.length_zipWith` in Std library -/
theorem length_zipWith' {β : Type v} {γ : Type w} (f : α → β → γ) (l₁ : List α) (l₂ : List β) : length (zipWith f l₁ l₂) = min l₁.length l₂.length :=
  l₂ |> l₁.rec
    (λ l₂ => l₂.zipWith_nil_first f ▸ l₂.length.zero_min.symm)
    λ a l₁ IH => fun
      | [] => (a::l₁).zipWith_nil_second f ▸ (a::l₁).length.min_zero'.symm
      | _::l₂ => (congrArg (·+1) (IH l₂)).trans (Nat.min_succ_succ' _ _).symm

theorem reverseAux_append_left {α : Type _} {as₁ as₂ bs : List α} : reverseAux (as₁ ++ as₂) bs = as₂.reverse ++ reverseAux as₁ bs := by
  revert bs; induction as₁ <;> intro bs
  case nil => rw [reverseAux_eq_append]; rfl
  case cons a₁ as₁ h_ind =>
    rw [cons_append]
    unfold reverseAux
    rw [h_ind]

theorem bind_congr {α β : Type _} : ∀ {as₁ as₂ : List α} {f₁ f₂ : α → List β}, as₁ = as₂ → (∀ a, f₁ a = f₂ a) → as₁.bind f₁ = as₂.bind f₂
| as, _, _, _, rfl, h =>
  congrArg (as.bind) (funext h)

theorem bind_map_binary_eq_map_bind_map {α β γ : Type _} (f : α → β → γ) (as : List α) (bs : List β) : as.bind (fun a => bs.map (f a)) = (as.map f).bind bs.map := by
  induction as with
  | nil => rfl
  | cons a as hi =>
    rw [cons_bind, map, cons_bind]
    rw [hi]


--- Lexicographical lift of relations
protected
inductive lex {α : Type _} (r : α → α → Prop) : List α → List α → Prop
| nil : (a : α) → (as : List α) → List.lex r [] (a::as)
| head {a b : α} {as bs : List α} : r a b → List.lex r (a::as) (b::bs)
| tail {a : α} {as bs : List α} : List.lex r as bs → List.lex r (a::as) (a::bs)

namespace lex

variable {α : Type _} {r : α → α → Prop}

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
  trichotCasesOn r a b
    (λ a h_ind =>
      Or.map (congrArg (List.cons a)) (Or.map List.lex.tail List.lex.tail) h_ind
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
