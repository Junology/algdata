/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Sigma
import Algdata.Data.List.Ascending

universe u v

/-!
  List of key-value pairs with values dependent on keys
  The elements are stored as the dependent pair `Sigma β` and sorted so that they form a chain of the given relation.
  Hence, it is implicitly assumed that the paramter `r : α → α → Prop` is an instance of `StrictLinearOrder` class defined in `Init.Order` in this library.
-/
structure KVChain {α : Type u} (r : α → α → Prop) (β : α → Type v) : Type (max u v) where
  toList : List (Sigma β)
  ascend : toList.Ascending (Sigma.relOnFst r)

attribute [unbox] KVChain
attribute [inline,reducible] KVChain.toList


namespace KVChain

variable {α : Type u} {r : α → α → Prop} {β : α → Type v}

@[reducible]
def boundLeft (a : α) (xs : KVChain r β) : Prop :=
  xs.toList.predHead (r a ∘ Sigma.fst)

@[reducible]
def boundRight (a : α) (xs : KVChain r β) : Prop :=
  xs.toList.predHead (flip r a ∘ Sigma.fst)

@[match_pattern, inline, reducible]
protected
def nil : KVChain r β :=
  {toList := [], ascend := List.Ascending.nil}

@[match_pattern, inline, reducible]
protected
def cons (a : α) (b : β a) (tail : KVChain r β) : tail.boundLeft a → KVChain r β :=
  λ hatail =>
    {toList := ⟨a,b⟩::tail.toList, ascend := tail.ascend.cons_of_head_tail hatail}

@[inline, reducible]
protected
def singleton (a : α) (b : β a) : KVChain r β := {
  toList := [⟨a,b⟩]
  ascend := List.Ascending.singleton _
}

def find? [DecidableEq α] (xs : KVChain r β) (a : α) : Option (β a) :=
  let rec loop : List (Sigma β) → Option (β a)
  | [] => none
  | (x::xs) => if h : (x.1=a) then some (h ▸ x.2) else loop xs
  loop xs.toList

@[inline, reducible]
def drop : Nat → KVChain r β → KVChain r β
| 0, x => x
| Nat.succ _, mk [] _ => KVChain.nil
| Nat.succ n, mk (_::as) ascend => KVChain.drop n ⟨as, ascend.tail⟩

@[inline, reducible]
def reverse : KVChain r β → KVChain (flip r) β
| mk toList ascend => {toList:=toList.reverse, ascend:=ascend.reverse}

--- `map` on key-value pairs with order-preserving operation on keys
--- @remark We do not provide `map` operation with non-order-preserving functions. Just use `List.map` together with `KVChain.fromList` defined in `Data.KVChain.MergeWith` module.
def mapKV {α₁ : Type _} {r₁ : α₁ → α₁ → Prop} {β₁ : α₁ → Type _} (f : α → α₁) (g : (a : α) → β a → β₁ (f a)) (f_rel : ∀ a b, r a b → r₁ (f a) (f b)) : KVChain r β → KVChain r₁ β₁
| mk toList ascend => {
  toList := toList.map (λ x => ⟨f x.1, g x.1 x.2⟩)
  ascend := ascend.map (Sigma.relOnFst r₁) (λ x => ⟨f x.1, g x.1 x.2⟩) $
    λ x y => f_rel x.1 y.1
}

def filterMapKV.{u₁, v₁} [Trans r r r] {α₁ : Type u₁} {r₁ : α₁ → α₁ → Prop} {β₁ : α₁ → Type v₁} (f : α → α₁) (g : (a : α) → β a → Option (β₁ (f a))) (f_rel : ∀ a b, r a b → r₁ (f a) (f b)) : KVChain r β → KVChain r₁ β₁
| mk toList ascend => {
  toList := toList.filterMap (λ x => match g x.1 x.2 with | none => none | some bg => some ⟨f x.1, bg⟩)
  ascend := by
    apply ascend.filterMap (Sigma.relOnFst r₁)
    intro x y hxy
    cases g x.1 x.2 <;> cases g y.1 y.2 <;> dsimp [Functor.map, Option.bind, Option.map] <;> try {exact Option.runP_none}
    apply Option.runP_some.mpr
    unfold Sigma.relOnFst at *
    exact f_rel _ _ hxy
}

--- `map` on the same keys
def mapVal {γ : α → Type _} (f : (a : α) → β a → γ a) : KVChain r β → KVChain r γ :=
  mapKV id f (λ _ _ => id)

@[inline]
def foldl {γ : Type _} (f : γ → (a : α) → β a → γ) (init : γ) (xs : KVChain r β) : γ :=
  xs.toList.foldl (λ c x => f c x.1 x.2) init

@[reducible]
def hingeable (xs : KVChain (flip r) β) (ys : KVChain r β) : Prop :=
  xs.toList.relHead (Sigma.relOnFst r) ys.toList

--- `(reverseAppend xs ys).toList = xs.toList.reverse ++ ys.toList`
def hinge (xs : KVChain (flip r) β) (ys : KVChain r β) : xs.hingeable ys → KVChain r β :=
  λ hhinge => {
    toList := List.reverseAux xs.toList ys.toList
    ascend := List.Ascending.reverseAux hhinge xs.ascend ys.ascend
  }

@[inline, reducible, elab_as_elim]
def recOnList
  {motive : KVChain r β → Sort _}
  (nil : motive KVChain.nil)
  (cons : (a : α) → (b : β a) → (xs : KVChain r β) → (haxs : xs.boundLeft a) → motive xs → motive (xs.cons a b haxs))
  (xs : KVChain r β)
  : motive xs :=
  let rec loop : (as : List (Sigma β)) → (ascend : as.Ascending (Sigma.relOnFst r)) → motive ⟨as, ascend⟩
  | [], _ => nil
  | (x::xs), ascend =>
    cons x.1 x.2 ⟨xs, ascend.tail⟩ ascend.head $
      loop xs ascend.tail
  loop xs.toList xs.ascend

@[inline, reducible, elab_as_elim]
def recOnListOn
  {motive : KVChain r β → Sort _}
  (xs : KVChain r β)
  (nil : motive KVChain.nil)
  (cons : (a : α) → (b : β a) → (xs : KVChain r β) → (haxs : xs.boundLeft a) → motive xs → motive (xs.cons a b haxs))
  : motive xs :=
  recOnList nil cons xs

theorem eq_of_toList_eq {x y : KVChain r β} : x.toList = y.toList → x = y :=
  match x, y with
  | mk xs xascend, mk ys _ =>
    λ h => by cases h; rw [proofIrrel xascend _]

@[simp]
theorem toList_nil : KVChain.nil.toList (r:=r) (β:=β) = [] :=
  rfl

@[simp]
theorem toList_cons {a : α} (b : β a) {xs : KVChain r β} {haxs : xs.boundLeft a} : (xs.cons a b haxs).toList = ⟨a,b⟩ :: xs.toList :=
  rfl

@[simp]
theorem boundLeft_descend {xs : KVChain r β} {a a₁ : α} : (∀ a', r a₁ a' → r a a') → xs.boundLeft a₁ → xs.boundLeft a :=
  λ haa₁ => List.predHead_of_predHead (λ _=> haa₁ _)

@[simp]
theorem cons_hingeable {a : α} {b : β a} {xs : KVChain (flip r) β} {haxs : xs.boundLeft a} {ys : KVChain r β} : (xs.cons a b haxs).hingeable ys = ys.boundLeft a := by
  unfold hingeable
  rw [List.relHead_cons_left]
  rfl

@[simp]
theorem hingeable_cons {xs : KVChain (flip r) β} {a : α} {b : β a} {ys : KVChain r β} {hay : ys.boundLeft a} : xs.hingeable (ys.cons a b hay) = xs.boundLeft a := by
  unfold hingeable
  rw [List.relHead_cons_right]
  rfl

@[simp]
theorem cons_hingeable_cons {a₁ : α} {b₁ : β a₁} {xs : KVChain (flip r) β} {ha₁xs: xs.boundLeft a₁} {a₂ : α} {b₂ : β a₂} {ys : KVChain r β} {ha₂ys : ys.boundLeft a₂} : (xs.cons a₁ b₁ ha₁xs).hingeable (ys.cons a₂ b₂ ha₂ys) = r a₁ a₂ := rfl

@[simp]
theorem hingeable_skip_right [Trans r r r] {xs : KVChain (flip r) β} {a : α} {b : β a} {ys : KVChain r β} {hays : ys.boundLeft a} : xs.hingeable (ys.cons a b hays) → xs.hingeable ys :=
  xs.recOnListOn
    id
    (λ a₁ _ _ _ _ => by
      rw [cons_hingeable, cons_hingeable]
      dsimp [boundLeft, List.predHead]
      dsimp [boundLeft, List.predHead] at hays
      cases hys : ys.toList
      case nil => intros; exact True.intro
      case cons => intro h; rw [hys] at hays; exact trans (t:=r) h hays
    )

@[simp]
theorem toList_hinge_eq_reverseAux {xs : KVChain (flip r) β} {ys : KVChain r β} {hxy : xs.hingeable ys} : (hinge xs ys hxy).toList = List.reverseAux xs.toList ys.toList := rfl

instance instCoeKVChainList : Coe (KVChain r β) (List (Sigma β)) :=
  Coe.mk KVChain.toList

instance instReprKVChain [Repr α] [(a : α) → Repr (β a)] : Repr (KVChain r β) where
  reprPrec xs prec := reprPrec xs.toList prec

instance instInhabitedKVChain : Inhabited (KVChain r β) :=
  Inhabited.mk KVChain.nil

protected
instance hasDecidableEq [DecidableEq α] [(a : α) → DecidableEq (β a)] : DecidableEq (KVChain r β) :=
  λ xs ys =>
    if h : xs.toList = ys.toList then
      isTrue $ eq_of_toList_eq h
    else
      isFalse $ λ hcontra => h (congrArg KVChain.toList hcontra)


--- Lexicographical order with respect to both keys and values
protected
def kvlex (s : (a : α) → β a → β a → Prop) : KVChain r β → KVChain r β → Prop :=
  InvImage (List.lex $ Sigma.lex r s) KVChain.toList

--- Lexicographical order with the opposite order on keys; which is equivalent to the lex-order considered with a virtual entry `(a,-∞)` for each absent key `a : α`.
protected
def rklex (s : (a : α) → β a → β a → Prop) : KVChain r β → KVChain r β → Prop :=
  InvImage (List.lex $ Sigma.lex (flip r) s) KVChain.toList

section lex

variable {s : (a : α) → β a → β a → Prop}

instance [Trans r r r] [(a : α) → Trans (s a) (s a) (s a)] : Trans (KVChain.kvlex (r:=r) s) (KVChain.kvlex s) (KVChain.kvlex s) :=
  instTransInvImage _ KVChain.toList

instance [Irreflective r] [(a : α) → Irreflective (s a)] : Irreflective (KVChain.kvlex (r:=r) s) :=
  instIrreflectiveInvImage _ KVChain.toList

instance [Asymmetry r] [(a : α) → Asymmetry (s a)] : Asymmetry (KVChain.kvlex (r:=r) s) :=
  instAsymmetryInvImage _ KVChain.toList

instance [Trichotomous r] [(a : α) → Trichotomous (s a)] : Trichotomous (KVChain.kvlex (r:=r) s) :=
  mkInstTrichotomousInvImage _ KVChain.toList $ @KVChain.eq_of_toList_eq _ _ _

instance [DecidableEq α] [DecidableRel r] [(a : α) → DecidableEq (β a)] [(a : α) → DecidableRel (s a)] : DecidableRel (KVChain.kvlex (r:=r) s) :=
  inferInstanceAs (DecidableRel (InvImage _ KVChain.toList))

protected
theorem kvlex.nil {a : α} {b : β a} {xs : KVChain r β} {haxs : xs.boundLeft a} : KVChain.kvlex s KVChain.nil (xs.cons a b haxs) :=
  List.lex.nil _ _

protected
theorem kvlex.headFst {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} {xs ys : KVChain r β} {haxs : xs.boundLeft a₁} {hays : ys.boundLeft a₂} : r a₁ a₂ → KVChain.kvlex s (xs.cons a₁ b₁ haxs) (ys.cons a₂ b₂ hays) :=
  λ h => List.lex.head (Sigma.lex.fst h)

protected
theorem kvlex.headSnd {a : α} {b₁ b₂ : β a} {xs ys : KVChain r β} {haxs : xs.boundLeft a} {hays : ys.boundLeft a} : s a b₁ b₂ → KVChain.kvlex s (xs.cons a b₁ haxs) (ys.cons a b₂ hays) :=
  λ h => List.lex.head (Sigma.lex.snd h)

protected
theorem kvlex.tail {a : α} {b : β a} {xs ys : KVChain r β} {haxs : xs.boundLeft a} {hays : ys.boundLeft a} : KVChain.kvlex s xs ys → KVChain.kvlex s (xs.cons a b haxs) (ys.cons a b hays) :=
  List.lex.tail

instance [Trans r r r] [(a : α) → Trans (s a) (s a) (s a)] : Trans (KVChain.rklex (r:=r) s) (KVChain.rklex s) (KVChain.rklex s) :=
  instTransInvImage _ KVChain.toList

instance [Irreflective r] [(a : α) → Irreflective (s a)] : Irreflective (KVChain.rklex (r:=r) s) :=
  instIrreflectiveInvImage _ KVChain.toList

instance [Asymmetry r] [(a : α) → Asymmetry (s a)] : Asymmetry (KVChain.rklex (r:=r) s) :=
  instAsymmetryInvImage _ KVChain.toList

instance [Trichotomous r] [(a : α) → Trichotomous (s a)] : Trichotomous (KVChain.rklex (r:=r) s) :=
  mkInstTrichotomousInvImage _ KVChain.toList $ @KVChain.eq_of_toList_eq _ _ _

instance [DecidableEq α] [DecidableRel r] [(a : α) → DecidableEq (β a)] [(a : α) → DecidableRel (s a)] : DecidableRel (KVChain.rklex (r:=r) s) :=
  inferInstanceAs (DecidableRel (InvImage _ KVChain.toList))

protected
theorem rklex.nil {a : α} {b : β a} {xs : KVChain r β} {haxs : xs.boundLeft a} : KVChain.rklex s KVChain.nil (xs.cons a b haxs) :=
  List.lex.nil _ _

protected
theorem rklex.headFst {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} {xs ys : KVChain r β} {haxs : xs.boundLeft a₁} {hays : ys.boundLeft a₂} : r a₂ a₁ → KVChain.rklex s (xs.cons a₁ b₁ haxs) (ys.cons a₂ b₂ hays) :=
  λ h => List.lex.head (Sigma.lex.fst h)

protected
theorem rklex.headSnd {a : α} {b₁ b₂ : β a} {xs ys : KVChain r β} {haxs : xs.boundLeft a} {hays : ys.boundLeft a} : s a b₁ b₂ → KVChain.rklex s (xs.cons a b₁ haxs) (ys.cons a b₂ hays) :=
  λ h => List.lex.head (Sigma.lex.snd h)

protected
theorem rklex.tail {a : α} {b : β a} {xs ys : KVChain r β} {haxs : xs.boundLeft a} {hays : ys.boundLeft a} : KVChain.rklex s xs ys → KVChain.rklex s (xs.cons a b haxs) (ys.cons a b hays) :=
  List.lex.tail

theorem rklex_not_nil_right {xs : KVChain r β} : ¬ KVChain.rklex s xs KVChain.nil :=
  λ hcontra => by cases xs; cases hcontra

@[elab_as_elim]
protected
theorem rklex.rec
  {motive : (xs ys : KVChain r β) → KVChain.rklex s xs ys → Prop}
  (nil : (a : α) → (b : β a) → (xs : KVChain r β) → (haxs : xs.boundLeft a) → motive KVChain.nil (xs.cons a b haxs) KVChain.rklex.nil)
  (headFst : (a₁ a₂ : α) → (b₁ : β a₁) → (b₂ : β a₂) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a₁) → (hays : ys.boundLeft a₂) → (ha₂a₁ : r a₂ a₁) → motive (xs.cons a₁ b₁ haxs) (ys.cons a₂ b₂ hays) (KVChain.rklex.headFst ha₂a₁))
  (headSnd : (a : α) → (b₁ b₂ : β a) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a) → (hays : ys.boundLeft a) → (hb₁b₂ : s a b₁ b₂) → motive (xs.cons a b₁ haxs) (ys.cons a b₂ hays) (KVChain.rklex.headSnd hb₁b₂))
  (tail : (a : α) → (b : β a) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a) → (hays : ys.boundLeft a) → (htail : KVChain.rklex s xs ys) → motive xs ys htail → motive (xs.cons a b haxs) (ys.cons a b hays) (KVChain.rklex.tail htail)) :
  ∀ {xs ys : KVChain r β} (h : KVChain.rklex s xs ys), motive xs ys h :=
  λ {xs ys} =>
    ys.recOnListOn
      (λ _ h => absurd h rklex_not_nil_right)
      (λ a₂ b₂ ys hays h_ind_ys xs =>
        xs.recOnListOn
          (λ _ => nil _ _ _ _)
          (λ a₁ b₁ xs haxs _ => by
            intro h
            dsimp [KVChain.rklex, InvImage] at h
            cases h
            case head hhead =>
              cases hhead
              case fst hheadFst => exact headFst _ _ _ _ _ _ _ _ hheadFst
              case snd hheadSnd => exact headSnd _ _ _ _ _ _ _ hheadSnd
            case tail htail =>
              have := h_ind_ys xs htail
              exact tail _ _ _ _ _ _ htail this
          )
      )
      xs

@[elab_as_elim]
protected
theorem rklex.recOn
  {motive : (xs ys : KVChain r β) → KVChain.rklex s xs ys → Prop}
  {xs ys : KVChain r β} (h : KVChain.rklex s xs ys)
  (nil : (a : α) → (b : β a) → (xs : KVChain r β) → (haxs : xs.boundLeft a) → motive KVChain.nil (xs.cons a b haxs) KVChain.rklex.nil)
  (headFst : (a₁ a₂ : α) → (b₁ : β a₁) → (b₂ : β a₂) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a₁) → (hays : ys.boundLeft a₂) → (ha₂a₁ : r a₂ a₁) → motive (xs.cons a₁ b₁ haxs) (ys.cons a₂ b₂ hays) (KVChain.rklex.headFst ha₂a₁))
  (headSnd : (a : α) → (b₁ b₂ : β a) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a) → (hays : ys.boundLeft a) → (hb₁b₂ : s a b₁ b₂) → motive (xs.cons a b₁ haxs) (ys.cons a b₂ hays) (KVChain.rklex.headSnd hb₁b₂))
  (tail : (a : α) → (b : β a) → (xs ys : KVChain r β) → (haxs : xs.boundLeft a) → (hays : ys.boundLeft a) → (htail : KVChain.rklex s xs ys) → motive xs ys htail → motive (xs.cons a b haxs) (ys.cons a b hays) (KVChain.rklex.tail htail)) :
  motive xs ys h :=
  KVChain.rklex.rec nil headFst headSnd tail h

end lex

end KVChain
