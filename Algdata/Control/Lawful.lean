/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

theorem map_seq {f : Type _ → Type _} [Applicative f] [LawfulApplicative f] {α β γ δ : Type _} {h : γ → δ} {g : α → β → γ} (x : f α) (y : f β) : (h <$> (g <$> x <*> y)) = ((fun a b => h (g a b)) <$> x <*> y) := by
  rw [←pure_seq, seq_assoc, map_pure, pure_seq, ←comp_map]
  apply congrArg
  rfl

theorem map_bind_eq_bind_comp {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α β γ : Type _} (f : α → β) (x : m α) (g : β → m γ) : (f <$> x >>= g) = x >>= (g ∘ f) := by
  rw [map_eq_pure_bind]
  rw [bind_assoc]
  rw [funext (fun x => pure_bind (f x) g)]
  rfl

theorem map_bind_eq_bind_map_comp {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α β γ : Type _} (g : β → γ) (f : α → m β) (x : m α) : g <$> (x >>= f) = x >>= (Functor.map (f:=m) g ∘ f) := by
  rw [map_eq_pure_bind]
  rw [bind_assoc]
  apply bind_congr
  intros a
  simp
  rw [map_eq_pure_bind]


/-!
## Instance for `Option`
-/
namespace Option

variable {α β γ : Type _}

@[simp]
theorem map_eq_bind_some_comp (f : α → β) (x : Option α) : f <$> x = bind x (some ∘ f) := by cases x <;> simp [Functor.map, Bind.bind, Option.bind, Option.map]

@[simp]
theorem bind_eq_bind (x : Option α) (f : α → Option β) : x >>= f = x.bind f := rfl

@[simp]
theorem pure_eq_some : pure (f:=Option) (α:=α) = some := rfl

@[simp]
theorem seq_eq_bind_map (f : Option (α → β)) (x : Option α) : f <*> x = f.bind (x.map) := rfl

@[simp]
theorem seqLeft_eq_fst_or_none (x : Option α) (y : Option β) : x <* y = y.casesOn (motive:=fun _ => Option α) none (fun _=> x):= by
  dsimp [SeqLeft.seqLeft]
  cases y <;> cases x <;> rfl

@[simp]
theorem seqRight_eq_none_or_snd (x : Option α) (y : Option β) : x *> y = x.casesOn (motive:=fun _ => Option β) none (fun _ => y) := by
  dsimp [SeqRight.seqRight]
  cases y <;> cases x <;> rfl

instance instLawfulMonadOption : LawfulMonad Option where
  map_const := rfl
  id_map a := by simp; cases a <;> rfl
  seqLeft_eq x y := by simp; cases x <;> cases y <;> rfl
  seqRight_eq x y := by simp; cases x <;> cases y <;> rfl
  pure_seq f x := by simp; cases x <;> rfl
  bind_pure_comp f x := by simp; cases x <;> rfl
  bind_map f x := by simp; cases f <;> cases x <;> rfl
  pure_bind x f := rfl
  bind_assoc x f g := by simp; cases x <;> rfl

end Option