/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Data.List.Basic
import Algdata.Data.List.Prop

set_option autoImplicit false

universe u v w

namespace List

/- Monad -/
instance instMonadList : Monad List where
  bind := List.bind
  pure a := [a]

/- LawfulMonad; i.e. monad laws -/
section LawfulMonad

variable {α β : Type u} {γ : Type w}

@[simp]
theorem pure_eq_singleton (a : α) : pure a = [a] := rfl

@[simp]
theorem map_eq_map (f : α → β) (as : List α) : f <$> as = as.map f := rfl

@[simp]
theorem bind_eq_bind (as : List α) (f : α → List β) : (as >>= f) = List.bind as f := rfl

@[simp]
theorem seq_eq_bind_map (fs : List (α → β)) (as : List α) : (fs <*> as) = List.bind fs as.map := rfl

@[simp]
theorem seqLeft_eq_bind_bind_const (as : List α) (bs : List β) : as <* bs = List.bind as (fun a => List.bind bs (Function.const β [a])):= rfl

@[simp]
theorem seqRight_eq_bind_const (as : List α) (bs : List β) : as *> bs = List.bind as (Function.const α bs) := rfl

@[simp]
theorem id_map (as : List α) : as.map id = as := by
  induction as with
  | nil => rfl
  | cons a as hi =>
    rw [map, hi]
    rfl

@[simp]
theorem bind_singleton_comp (f : α → β) : ∀ (as : List α), as.bind (fun a => [f a]) = as.map f
| [] => rfl
| (a::as) => by
  rw [cons_bind, map]
  rw [cons_append, nil_append]
  rw [bind_singleton_comp f as]

@[simp]
theorem singleton_bind (a : α) (f : α → List β) : [a].bind f = f a := by
  rw [List.bind, map, map, join, join]
  simp

@[simp]
theorem bind_assoc (as : List α) (f : α → List β) (g : β → List γ) : ((as.bind f).bind g) = as.bind fun x => (f x).bind g := by
  induction as with
  | nil => rfl
  | cons a as hi =>
    rw [cons_bind, cons_bind]
    rw [append_bind]
    rw [hi]

instance instLawfulMonadList : LawfulMonad List where
  id_map as := List.id_map as
  map_const := by intros; rfl
  seqLeft_eq {α} {β} as bs := by
    rw [seqLeft_eq_bind_bind_const]
    rw [seq_eq_bind_map]
    rw [map_eq_map]
    have : (fun (a : α) => bs.bind (Function.const _ [a])) = fun (a : α) => bs.map (Function.const _ a) := by
      apply funext; intro a
      rw [←bind_singleton_comp (Function.const β a) bs]
      rfl
    rw [this]; clear this
    rw [bind_map_binary_eq_map_bind_map]
  seqRight_eq as bs := by
    rw [seqRight_eq_bind_const]
    rw [seq_eq_bind_map]
    rw [map_eq_map]
    rw [←bind_map_binary_eq_map_bind_map]
    apply congrArg
    simp
    rfl
  pure_seq f as := by
    rw [seq_eq_bind_map]
    rw [pure_eq_singleton, map_eq_map]
    rw [singleton_bind]
  bind_pure_comp {α} {β} f as := by
    rw [bind_eq_bind]
    rw [funext (fun a=> pure_eq_singleton (f a))]
    rw [map_eq_map]
    rw [bind_singleton_comp]
  bind_map f as := by
    rw [bind_eq_bind]
    rw [funext (fun a=> map_eq_map a as)]
    rw [seq_eq_bind_map]
  pure_bind := singleton_bind
  bind_assoc := bind_assoc

end LawfulMonad


end List
