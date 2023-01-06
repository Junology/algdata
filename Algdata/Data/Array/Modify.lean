/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Classes.LawfulMonad

import Algdata.Data.Array.Lemmas

namespace Array

universe u v

variable {m : Type u → Type v} [Monad m] {α : Type u}

@[simp]
theorem modifyM_nil (n : Nat) (f : α → m α) : #[].modifyM n f = pure #[] := by
  rfl

@[simp]
theorem modifyM_head (a : α) (as : List α) (f : α → m α) : modifyM {data := a::as} 0 f = (f a >>= fun a' => pure {data := a' :: as }) := by
  dsimp [modifyM]
  rw [dif_pos (Nat.zero_lt_succ _)]
  conv =>
    lhs; lhs; change f a

-- modifyM with an out-of-range index
theorem modifyM_oor (x : Array α) (n : Nat) (f : α → m α) : ¬(n < x.size) → x.modifyM n f = pure x := by
  intro h
  rw [modifyM, dif_neg h]

theorem modifyM_tail [LawfulMonad m] {α : Type _} (a : α) (as : List α) (n : Nat) (f : α → m α) : Array.modifyM {data := a::as} n.succ f = #[a].append <$> (Array.modifyM {data := as} n f) := by
  by_cases n < as.length
  case pos hpos =>
    dsimp [modifyM, modifyM]
    have : n.succ < size {data := as} + 1 :=
      Nat.succ_lt_succ hpos
    rw [dif_pos this, dif_pos hpos]
    rw [bind_pure_comp, bind_pure_comp, ←comp_map]
    apply map_congr
    intro a
    rw [set_cons_succ']
    rfl
  case neg hneg =>
    rw [modifyM_oor {data := as} n f hneg]
    have : ¬(n.succ < size {data := a::as}) := hneg ∘ Nat.lt_of_succ_lt_succ
    rw [modifyM_oor {data := a::as} n.succ f this]
    simp
    apply congrArg
    apply Array.eq
    conv =>
      rhs; rw [append_data]; change [a] ++ as; change a::as

@[simp]
theorem modify_nil (n : Nat) (f : α → α) : Array.modify #[] n f = #[] := by
  rw [modify, Id.run, modifyM_nil]
  rfl

@[simp]
theorem modify_head (a : α) (as : List α) (f : α → α) : Array.modify {data := a::as} 0 f = {data := f a :: as} := by
  rw [modify, Id.run, modifyM_head]
  rfl

theorem modify_oor (x : Array α) (n : Nat) (f : α → α) (h : ¬(n < x.size)) : x.modify n f = x := by
  rw [modify, Id.run, modifyM_oor (m:=Id) x n f h]
  rfl

@[simp]
theorem modify_tail (a : α) (as : List α) {k : Nat} {f : α → α} : Array.modify {data := a::as} k.succ f = #[a].append (modify {data := as} k f) := by
  rw [modify, Id.run, modify, Id.run]
  exact modifyM_tail (m:=Id) a as k f

theorem size_modifyM [LawfulMonad m] {α : Type _} : ∀ (x : Array α) (n : Nat) (f : α → m α), SatisfiesM (fun y => y.size = x.size) (x.modifyM n f)
| mk as => by
  induction as with
  | nil =>
    intros n f
    exists pure (f:=m) (Subtype.mk (p:=fun y => y.size = (mk (α:=α) []).size) (mk (α:=α) []) rfl)
    have : mk (α:=α) [] = #[] := rfl
    rw [this, modifyM_nil]; clear this
    rw [map_pure]
  | cons a as hi =>
    intros n f
    cases n with
    | zero =>
      simp
      exists f a >>= fun a' => pure (Subtype.mk (p:=fun y => y.size = as.length.succ) (mk (a'::as)) rfl)
      rw [bind_pure_comp, bind_pure_comp]
      rw [←comp_map]
      rfl
    | succ n =>
      rw [modifyM_tail]
      apply SatisfiesM.map (p:=λ y => y.size = as.length)
      . cases hi n f with | intro w hw =>
        exact Exists.intro w hw
      . intros y hy;
        conv =>
          lhs; change size (#[a] ++ y);
          rw [size_eq_length_of_data, append_data, List.length_append]
          change 1 + y.size; rw [hy]
        exact Nat.add_comm 1 _

@[simp]
theorem size_modify : ∀ (x : Array α) (n : Nat) (f : α → α), (x.modify n f).size = x.size := by
  intro x n f
  cases size_modifyM (m:=Id) x n f with | intro w hw =>
  dsimp at hw
  conv at hw => rhs; change modify x n f
  rw [←hw]
  exact w.property

end Array
