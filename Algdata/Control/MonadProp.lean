/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Control.Lawful
import Algdata.Control.Prop

-- Monad which can choose a proof of a proposition for each value
class MonadProp (m : Type _ → Type _) [Functor m] where
  (ensure : {α : Type _} → {p : α → Prop} → (x : m α) → p <$? x → m (Subtype p))
  (val_ensure : ∀ {α : Type _} {p : α → Prop} (x : m α) (h : mapP p x), Subtype.val <$> ensure x h = x)

namespace MonadProp

variable {m : Type _ → Type _} [Monad m] [LawfulMonad m] [MonadProp m]

theorem mapP_of_bind {α β : Type _} {p : α → Prop} {q : β → Prop} (x : m α) (f : α → m β) : p <$? x → (∀ a, p a → q <$? f a) → q <$? (x >>= f) := by
  intro hx hfx
  cases hx with | intro wp hwp =>
  cases hwp
  rw [map_bind_eq_bind_comp (f:=Subtype.val)]
  exists (wp >>= fun c => ensure (f c.val) (hfx c.val c.property))
  rw [map_bind_eq_bind_map_comp]
  apply bind_congr
  intros a
  simp
  rw [val_ensure]

end MonadProp


/-!
## `Id`
-/

namespace Id

theorem mapP_iff_id {α : Type _} {p : α → Prop} : ∀ a, mapP (f:=Id) p a ↔ p a := by
  intro a
  constructor
  case mp =>
    intro ha; cases ha with | intro w hw =>
    exact hw ▸ w.property
  case mpr =>
    intro ha
    exact ⟨Subtype.mk (p:=p) a ha, rfl⟩

theorem mapP_eq_id {α : Type _} (p : α → Prop) : mapP (f:=Id) p = p :=
  funext $ fun a => propext (mapP_iff_id a)

instance instMonadPropId : MonadProp Id where
  ensure a ha := Subtype.mk a $
    ha.elim (fun x hx => hx ▸ x.property)
  val_ensure _ _ := rfl

end Id


/-!
## `Option`
-/

namespace Option

variable {α : Type _}

def noneOrTrue (p : α → Prop) (x : Option α) : Prop :=
  x.rec (motive:=fun _ => Prop) True p

theorem mapP_iff_noneOrTrue {p : α → Prop} {x : Option α} : p <$? x ↔ noneOrTrue p x := by
  constructor
  case mp =>
    intro h
    cases h with | intro w hw =>
    cases hw
    cases w with
    | none => simp; rw [Option.bind, noneOrTrue]; simp
    | some a => simp; rw [Option.bind, noneOrTrue]; exact a.property
  case mpr =>
    intro h
    cases x with
    | none =>
      exists none (α:=Subtype p)
    | some a =>
      exists some (α:=Subtype p) ⟨a,h⟩

def ensure {p : α → Prop} : (x : Option α) → p <$? x → Option (Subtype p)
| none, _ => none
| some a, h => some ⟨a,mapP_iff_noneOrTrue.mp h⟩

instance instMonadPropOption : MonadProp Option where
  ensure := ensure
  val_ensure x hx := by cases x <;> rfl
end Option


/-!
## `ExceptT`
-/

namespace ExceptT

variable {α β ε : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m] [MonadProp m]

def errorOrApply (f : α → β) : Except ε α → Except ε β
| Except.error e => Except.error e
| Except.ok a => Except.ok (f a)

theorem map_eq_map_error_or_apply (f : α → β) (x : ExceptT ε m α) : (Functor.map (f:=ExceptT ε m) f x) = errorOrApply f <$> x := by
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative]
  unfold instMonadExceptT
  simp
  unfold ExceptT.map
  rw [map_eq_pure_bind]
  apply bind_congr
  intro e <;> cases e <;> rfl

def is_error_or_true (p : α → Prop) : Except ε α → Prop :=
  fun e => e.casesOn (motive:=fun _ => Prop) (fun _ => True) p

def toSubtype{p : α → Prop} : Except ε (Subtype p) → Subtype (is_error_or_true (ε:=ε) p)
| Except.error e =>
  Subtype.mk (Except.error e) $ by
    unfold is_error_or_true
    simp
| Except.ok a =>
  Subtype.mk (Except.ok a.val) $ by
    unfold is_error_or_true
    simp
    exact a.property

def fromSubtype {p : α → Prop} : Subtype (is_error_or_true (ε:=ε) p) → Except ε (Subtype p)
| Subtype.mk (Except.error e) _ => Except.error e
| Subtype.mk (Except.ok a) ha => Except.ok ⟨a,ha⟩

theorem is_error_or_true_apply (p : β → Prop) (f : α → β) : (is_error_or_true (ε:=ε) p ∘ errorOrApply f) = is_error_or_true (p ∘ f) := by
  apply funext
  intros e <;> cases e <;> rfl

theorem mapP_iff_error_or_true {α : Type _} {p : α → Prop} : ∀ x, mapP (f:=ExceptT ε m) p x ↔ mapP (f:=m) (is_error_or_true p) x := by
  intro x
  constructor
  case mp =>
    intro hx
    cases hx with | intro w hw =>
    cases hw
    exists toSubtype <$> w
    rw [←comp_map]
    rw [map_eq_map_error_or_apply]
    apply map_congr
    intro e <;> cases e <;> rfl
  case mpr =>
    intro hx
    cases hx with | intro w hw =>
    cases hw
    unfold mapP
    exists Functor.map (f:=m) fromSubtype w
    rw [map_eq_map_error_or_apply, ←comp_map]
    apply map_congr
    intro e <;> cases e with | mk e he =>
    cases e <;> rfl

def ensure {α : Type} {p : α → Prop} (x : ExceptT ε m α) (hx : p <$? x) : ExceptT ε m (Subtype p) :=
  Functor.map (f:=m) fromSubtype $
    MonadProp.ensure (m:=m) x $
      (mapP_iff_error_or_true x).mp hx

instance instMonadPropExceptT : MonadProp (ExceptT ε m) where
  ensure := ensure
  val_ensure {α} {p} x hx := by
    unfold ensure
    rw [map_eq_map_error_or_apply]
    rw [←comp_map]
    have : errorOrApply (ε:=ε) (Subtype.val (p:=p)) ∘ fromSubtype = Subtype.val := by
      apply funext
      intro e <;> cases e with | mk e he =>
      cases e <;> rfl
    rw [this]
    rw [MonadProp.val_ensure (m:=m) x]

end ExceptT


/-!
## `ReaderT`
-/

namespace ReaderT

variable {ρ α β : Type _} {m : Type _ → Type _} [Monad m] [MonadProp m]

def ensure {p : α → Prop} (x : ReaderT ρ m α) (hx : p <$? x) : ReaderT ρ m (Subtype p) :=
  fun r =>
    MonadProp.ensure (m:=m) (x r) $ by
      cases hx with | intro x hx =>
      cases hx
      unfold mapP
      exists x r

theorem map_eq_map_ap (f : α → β) (x : ReaderT ρ m α) : ∀ r, (f <$> x) r = f <$> (x r) := fun _ => rfl

instance instMonadPropReaderT : MonadProp (ReaderT ρ m) where
  ensure := ensure
  val_ensure {α} {p} x hx := by
    apply funext
    intro r
    cases hx with | intro w hw =>
    cases hw
    unfold ensure
    simp
    rw [map_eq_map_ap, MonadProp.val_ensure]

end ReaderT


/-!
## `StateRefT`
-/

instance {ω σ : Type _} {m : Type _ → Type _} [Monad m] [MonadProp m] : MonadProp (StateRefT' ω σ m) :=
  inferInstanceAs (MonadProp (ReaderT (ST.Ref ω σ) m))


/-!
## `StateT`
-/

namespace StateT

universe u
variable {σ : Type _} {α β : Type _} {m : Type u → Type _} [Monad m] [LawfulMonad m] [MonadProp m]

theorem map_eq_map_comp (f : α → β) (x : StateT σ m α) : (f <$> x) = Functor.map (f:=m) (Prod.map f id) ∘ x := by
  apply funext; intro s
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative]
  unfold instMonadStateT
  simp
  unfold StateT.map
  rw [map_eq_pure_bind]
  apply bind_congr
  intro w; rfl

theorem mapP_eq_forall_mapP_fst {p : α → Prop} {x : StateT σ m α} : (p <$? x) = ∀ s, (p ∘ Prod.fst) <$? (x s) := by
  apply propext; constructor
  case a.mp =>
    intro hx s
    cases hx with | intro w hw =>
    cases hw
    exists Subtype.fromProdRight <$> w s
    rw [←comp_map, map_eq_map_comp]
    simp
    apply map_congr
    intro x; rfl
  case a.mpr =>
    intro h
    exists fun s => Subtype.toProdRight <$> MonadProp.ensure (x s) (h s)
    apply funext; intro s
    rw [map_eq_map_comp]
    simp
    rw [←comp_map, Subtype.map_val_toProdRight]
    rw [MonadProp.val_ensure (x s) (h s)]

def ensure {p : α → Prop} (x : StateT σ m α) (hx : p <$? x) : StateT σ m (Subtype p) :=
  let hx' : ∀ s, (p ∘ Prod.fst) <$? (x s) := by
    rw [mapP_eq_forall_mapP_fst] at hx
    exact hx
  fun s => Subtype.toProdRight <$> MonadProp.ensure (x s) (hx' s)

instance instMonadPropStateT : MonadProp (StateT σ m) where
  ensure := ensure
  val_ensure x hx := by
    apply funext; intro s
    unfold ensure
    rw [map_eq_map_comp]
    simp
    rw [←comp_map, Subtype.map_val_toProdRight]
    exact MonadProp.val_ensure _ _

end StateT


/-!
## `EStateM`
-/

namespace EStateM

variable {ε σ α : Type _}

namespace Result

def map {β : Type _} (f : α → β) (x : Result ε σ α) : Result ε σ β :=
  x.casesOn (motive:=fun _ => Result ε σ β)
    (fun a s => ok (f a) s)
    (fun e s => error (α:=β) e s)

def errorOrTrue (p : α → Prop) : Result ε σ α → Prop :=
  fun x => x.casesOn (motive:=fun _ => Prop)
    (fun a _ => p a)
    (fun _ _ => True)

theorem errorOrTrue_ok {p : α → Prop} {x : Result ε σ α} {a : α} {s : σ} : x = ok a s → x.errorOrTrue p → p a := by
  intro ha; cases ha
  unfold errorOrTrue
  exact id

def fromSubtype {p : α → Prop} : Subtype (errorOrTrue (ε:=ε) (σ:=σ) p) → Result ε σ (Subtype p)
| Subtype.mk (ok a s) h => ok ⟨a,h⟩ s
| Subtype.mk (error e s) _ => error e s

theorem map_val_fromSubtype {p : α → Prop} (x : Subtype (errorOrTrue (ε:=ε) (σ:=σ) p)) : map Subtype.val (fromSubtype x) = x.val := by
  cases x with | mk a ha =>
  unfold fromSubtype; unfold map
  cases a <;> simp

end Result

theorem map_eq_map_comp {β : Type _} (f : α → β) (x : EStateM ε σ α) : (f <$> x) = Result.map f ∘ x := by
  apply funext; intro s
  rw [Functor.map, Applicative.toFunctor, Monad.toApplicative, instMonadEStateM]
  simp
  unfold EStateM.map
  cases x s <;> unfold Result.map <;> rfl

theorem mapP_iff_forall_error_or_true {p : α → Prop} {x : EStateM ε σ α} : (p <$? x) ↔ ∀ s, (x s).errorOrTrue p := by
  constructor
  case mp =>
    intro hx s
    cases hx with | intro w hw =>
    cases hw
    rw [Functor.map, Applicative.toFunctor, Monad.toApplicative, instMonadEStateM]
    simp
    unfold EStateM.map
    cases w s with
    | ok a s =>
      unfold Result.errorOrTrue; simp
      exact a.property
    | error e s => unfold Result.errorOrTrue; simp
  case mpr =>
    intro h
    exists fun s => Result.fromSubtype ⟨x s, h s⟩
    apply funext
    intro s
    rw [map_eq_map_comp]
    simp
    rw [Result.map_val_fromSubtype]

def ensure {p : α → Prop} (x : EStateM ε σ α) (hx : p <$? x) : EStateM ε σ (Subtype p) :=
  fun s =>
    Result.fromSubtype $ Subtype.mk (x s) $
      mapP_iff_forall_error_or_true.mp hx s

instance instMonadPropEStateM : MonadProp (EStateM ε σ) where
  ensure := ensure
  val_ensure x hx := by
    apply funext; intro s
    cases hx with | intro w hw =>
    cases hw
    rw [map_eq_map_comp]
    simp
    unfold ensure
    rw [Result.map_val_fromSubtype]

end EStateM

