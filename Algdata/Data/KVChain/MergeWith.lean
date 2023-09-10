/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Tactic.PkgLocal
import Algdata.Init.Order
import Algdata.Data.KVChain.Basic

pkg_include List.reverseAux_append_left

/-!
# Merge two `KVChain`s
-/

namespace KVChain

universe u v

variable {α : Type u} {r : α → α → Prop} [StrictLinearOrder r] [DecidableRel r] {β : α → Type v}

set_option autoImplicit false


/-!
## Insertion of an element to `KVChain`
-/

def insertWithAux (f : (a : α) → β a → β a → Option (β a)) (xs : KVChain (flip r) β) (ys : KVChain r β) (hxsys : xs.hingeable ys) (a : α) (b : β a) (hxsa : xs.boundLeft a) : {z : KVChain (flip r) β × KVChain r β // z.1.hingeable z.2} :=
  let rec loop : (xs : KVChain (flip r) β) → (ys : List (Sigma β)) → ys.Ascending (Sigma.relOnFst r) → ys.predHead (xs.boundLeft ∘ Sigma.fst) → xs.boundLeft a → {z : KVChain (flip r) β × KVChain r β // z.1.hingeable z.2}
  | xs, [], _, _, hxsa =>
    Subtype.mk (xs.cons a b hxsa, KVChain.nil) $ True.intro
  | xs, yys@(y::ys), hascend, hxsyys, hxsa =>
    if hya : r y.1 a then
      loop (xs.cons y.1 y.2 hxsyys) ys hascend.tail hascend.head hya
    else if hay : r a y.1 then
      Subtype.mk (xs.cons a b hxsa, ⟨yys, ‹yys=_› ▸ hascend⟩) (‹yys=_›.symm ▸ hay)
    else
      have heq : a = y.1 := Trichotomous.eq_of_incomp ⟨hay, hya⟩
      match f y.1 y.2 (heq▸b) with
      | none =>
        Subtype.mk (xs, ⟨ys,hascend.tail⟩) $ by
          apply hingeable_skip_right (xs:=xs) (a:=y.1) (b:=y.2) (ys:=⟨ys,hascend.tail⟩) (hays:=hascend.head)
          dsimp [hingeable]
          rw [List.relHead_eq_predHead_predHead]
          exact hxsyys
      | some z =>
        Subtype.mk (xs.cons y.1 z hxsyys, ⟨ys, hascend.tail⟩) $
          cons_hingeable (haxs:=hxsyys) ▸ hascend.head
  loop xs ys.toList ys.ascend (List.relHead_eq_predHead_predHead ▸ hxsys) hxsa

def insertWith (f : (a : α) → β a → β a → Option (β a)) (xs : KVChain r β) (a : α) (b : β a) : KVChain r β :=
  match insertWithAux f KVChain.nil xs True.intro a b True.intro with
  | Subtype.mk z hz => KVChain.hinge z.1 z.2 hz

def fromListWith (f : (a : α) → β a → β a → Option (β a)) (ys : List (Sigma β)) : KVChain r β :=
  ys.foldl (λ xs y => xs.insertWith f y.1 y.2) KVChain.nil


section Theorems

variable {f : (a : α) → β a → β a → Option (β a)}

@[simp]
theorem insertWithAux_nil {xs : KVChain (flip r) β} : ∀ {hxnil : xs.hingeable KVChain.nil} {a : α} {b : β a} {haxs : xs.boundLeft a}, insertWithAux f xs KVChain.nil hxnil a b haxs = ⟨(xs.cons a b haxs, KVChain.nil), True.intro⟩ := by
  intros; rfl

theorem insertWithAux_cons_rel {xs : KVChain (flip r) β} {a₁ : α} {b₁ : β a₁} {ys : KVChain r β} {ha₁ys : ys.boundLeft a₁} {ha₁xs : xs.hingeable (ys.cons a₁ b₁ ha₁ys)} {a : α} {b : β a} {haxs : xs.boundLeft a} : ∀ (ha₁a : r a₁ a), insertWithAux f xs (ys.cons a₁ b₁ ha₁ys) ha₁xs a b haxs = insertWithAux f (xs.cons a₁ b₁ (hingeable_cons ▸ ha₁xs)) ys (cons_hingeable.symm ▸ ha₁ys) a b ha₁a := by
  intro hbc
  unfold insertWithAux
  conv in KVChain.cons a₁ b₁ ys ha₁ys => unfold KVChain.cons
  dsimp [insertWithAux.loop]
  rw [dif_pos hbc]

theorem insertWithAux_cons_flip {xs : KVChain (flip r) β} {a₁ : α} {b₁ : β a₁} {ys : KVChain r β} {ha₁ys : ys.boundLeft a₁} {ha₁xs : xs.hingeable (ys.cons a₁ b₁ ha₁ys)} {a : α} {b : β a} {haxs : xs.boundLeft a} : ∀ (haa₁ : r a a₁), insertWithAux f xs (ys.cons a₁ b₁ ha₁ys) ha₁xs a b haxs = ⟨(xs.cons a b haxs, ys.cons a₁ b₁ ha₁ys), haa₁⟩ := by
  intro haa₁
  unfold insertWithAux
  conv in KVChain.cons a₁ b₁ ys ha₁ys => unfold KVChain.cons
  dsimp [insertWithAux.loop]
  rw [dif_neg (Asymmetry.asymm _ _ haa₁), dif_pos haa₁]

theorem insertWithAux_cons_rfl {xs : KVChain (flip r) β} {a : α} {b₁ : β a} {ys : KVChain r β} {hays : ys.boundLeft a} {haxs : xs.hingeable (ys.cons a b₁ hays)} {b : β a} {haxs' : xs.boundLeft a}: insertWithAux f xs (ys.cons a b₁ hays) haxs a b haxs' = (f a b₁ b).casesOn ⟨(xs, ys), hingeable_skip_right haxs⟩ (λ bf => ⟨(xs.cons a bf haxs', ys), Eq.symm (cons_hingeable (a:=a) (xs:=xs) (haxs:=haxs')) ▸ hays⟩) := by
  unfold insertWithAux
  conv in KVChain.cons a b₁ ys => unfold KVChain.cons
  dsimp [insertWithAux.loop]
  rw [dif_neg (Irreflective.irrefl (r:=r) _), dif_neg (Irreflective.irrefl (r:=r) _)]
  cases hf : f a b₁ b <;> rfl

theorem toList_fst_insertWithAux_eq_append {xs : KVChain (flip r) β} {ys : KVChain r β} {hxsys : xs.hingeable ys} {a : α} {b : β a} {haxs : xs.boundLeft a} : (insertWithAux f xs ys hxsys a b haxs).val.fst.toList = (insertWithAux f KVChain.nil ys True.intro a b True.intro).val.fst.toList ++ xs.toList := by
  revert xs
  apply ys.recOnList (motive:=λ ys=>∀ xs hxsys haxs, (insertWithAux f xs ys hxsys a b haxs).val.fst.toList = (insertWithAux f KVChain.nil ys True.intro a b True.intro).val.fst.toList ++ xs.toList)
  case nil => intros; rfl
  case cons =>
    intro a₁ b₁ ys ha₁ys h_ind xs ha₁xs haxs
    apply dite (r a₁ a) <;> intro ha₁a
    . rw [insertWithAux_cons_rel ha₁a]
      rw [insertWithAux_cons_rel ha₁a]
      rw [h_ind (xs.cons a₁ b₁ _), h_ind ⟨[⟨a₁,b₁⟩], _⟩]
      rw [KVChain.toList_cons]
      dsimp
      rw [List.append_cons]
    . apply dite (r a a₁) <;> intro haa₁
      . rw [insertWithAux_cons_flip haa₁]
        rw [insertWithAux_cons_flip haa₁]
        rfl
      . have : a = a₁ := Trichotomous.eq_of_incomp ⟨haa₁, ha₁a⟩
        cases this
        rw [insertWithAux_cons_rfl]
        rw [insertWithAux_cons_rfl]
        cases f a b₁ b <;> rfl

theorem toList_snd_insertWithAux_inv {xs : KVChain (flip r) β} {ys : KVChain r β} {hxsys : xs.hingeable ys} {a : α} {b : β a} {haxs : xs.boundLeft a} : (insertWithAux f xs ys hxsys a b haxs).val.snd = (insertWithAux f KVChain.nil ys True.intro a b True.intro).val.snd := by
  revert xs
  apply ys.recOnList (motive:=λ ys =>∀ xs hxsys haxs, (insertWithAux f xs ys hxsys a b haxs).val.snd = (insertWithAux f KVChain.nil ys True.intro a b True.intro).val.snd)
  case nil => intros; rfl
  case cons =>
    intro a₁ b₁ ys ha₁ys h_ind xs hxsys haxs
    apply dite (r a₁ a) <;> intro ha₁a
    . rw [insertWithAux_cons_rel ha₁a]
      rw [insertWithAux_cons_rel ha₁a]
      rw [h_ind, h_ind ⟨[⟨a₁,b₁⟩], _⟩]
    . apply dite (r a a₁) <;> intro haa₁
      . rw [insertWithAux_cons_flip haa₁]
        rw [insertWithAux_cons_flip haa₁]
      . have : a = a₁ := Trichotomous.eq_of_incomp ⟨haa₁, ha₁a⟩
        cases this
        rw [insertWithAux_cons_rfl]
        rw [insertWithAux_cons_rfl]
        cases f a b₁ b <;> rfl

theorem forAll_fst_insertWithAux {xs : KVChain (flip r) β} {ys : KVChain r β} {hxsys : xs.hingeable ys} {a : α} {b : β a} {haxs : xs.boundLeft a} : ∀ {p : α → Prop}, xs.toList.forAll (p ∘ Sigma.fst) → ys.toList.forAll (p ∘ Sigma.fst) → p a → (insertWithAux f xs ys hxsys a b haxs).val.fst.toList.forAll (p ∘ Sigma.fst) ∧ (insertWithAux f xs ys hxsys a b haxs).val.snd.toList.forAll (p ∘ Sigma.fst) := by
  intro p; revert xs;
  apply ys.recOnList (motive:=λ ys=>∀ xs hxsys haxs, xs.toList.forAll (p ∘ Sigma.fst) → ys.toList.forAll (p ∘ Sigma.fst) → p a → (insertWithAux f xs ys hxsys a b haxs).val.fst.toList.forAll (p ∘ Sigma.fst) ∧ (insertWithAux f xs ys hxsys a b haxs).val.snd.toList.forAll (p ∘ Sigma.fst))
  case nil =>
    intro xs hxsys haxs hpxs _ hpa
    dsimp [insertWithAux, insertWithAux.loop]
    exact ⟨⟨hpa, hpxs⟩, True.intro⟩
  case cons =>
    intro a₁ b₁ ys ha₁ys h_ind xs ha₁xs hzxs hpxs hpys hpa
    apply dite (r a₁ a) <;> intro ha₁a
    . rw [insertWithAux_cons_rel ha₁a]
      exact h_ind (xs.cons a₁ b₁ (hingeable_cons ▸ ha₁xs)) (cons_hingeable.symm ▸ ha₁ys) ha₁a ⟨hpys.left, hpxs⟩ hpys.right hpa
    . apply dite (r a a₁) <;> intro haa₁
      . rw [insertWithAux_cons_flip haa₁]
        dsimp
        exact ⟨⟨hpa,hpxs⟩,hpys⟩
      . have : a = a₁ := Trichotomous.eq_of_incomp ⟨haa₁, ha₁a⟩
        cases this
        rw [insertWithAux_cons_rfl]
        cases f a b₁ b
        case none => exact ⟨hpxs, hpys.right⟩
        case some bf => exact ⟨⟨hpys.left, hpxs⟩, hpys.right⟩

theorem boundLeft_insertWithAux_fst {xs : KVChain (flip r) β} {ys : KVChain r β} {hxsys : xs.hingeable ys} {a : α} {b : β a} {haxs : xs.boundLeft a} : ∀ {c : α}, r a c → (insertWithAux f xs ys hxsys a b haxs).val.fst.boundLeft c := by
  intro c hac
  revert xs
  apply ys.recOnList (motive:=λ ys=>∀ xs hxsys haxs, (insertWithAux f xs ys hxsys a b haxs).val.fst.boundLeft c)
  case nil =>
    intros; dsimp; exact hac
  case cons =>
    intro a₁ b₁ ys ha₁ys h_ind xs ha₁xs haxs
    apply dite (r a₁ a) <;> intro ha₁a
    . rw [insertWithAux_cons_rel ha₁a]
      exact h_ind _ (cons_hingeable.symm ▸ ha₁ys) (by exact ha₁a)
    . apply dite (r a a₁) <;> intro haa₁
      . rw [insertWithAux_cons_flip haa₁]
        exact hac
      . have : a = a₁ := Trichotomous.eq_of_incomp ⟨haa₁, ha₁a⟩
        cases this
        rw [insertWithAux_cons_rfl]
        cases f a b₁ b
        case none =>
          apply boundLeft_descend _ haxs
          exact λ _ => flip (trans (r:=r) (s:=r) (t:=r)) hac
        case some bf => exact hac

@[simp]
theorem insertWith_nil : ∀ {a : α} {b : β a}, insertWith (r:=r) f KVChain.nil a b = ⟨[⟨a,b⟩], List.Ascending.singleton _⟩ := rfl

theorem boundLeft_insertWith_of_boundLeft {xs : KVChain r β} {a : α} {b : β a} : ∀ (d : α), xs.boundLeft d → r d a → (xs.insertWith f a b).boundLeft d := by
  apply xs.recOnList (motive:=λ xs=>∀ d, xs.boundLeft d → r d a → (xs.insertWith f a b).boundLeft d)
  case nil =>
    intro a _ hab
    rw [insertWith_nil]
    exact hab
  case cons =>
    intro a₁ b₁ xs ha₁xs _ d hdxs hda
    unfold insertWith
    dsimp [boundLeft]
    apply List.predHead_of_forAll
    rw [List.forAll_reverseAux]
    apply forAll_fst_insertWithAux
    . exact True.intro
    . apply (xs.cons a₁ b₁ ha₁xs).ascend.forAll_of_predHead
      . exact λ _ _ h₁ h₂ => trans (t:=r) h₁ h₂
      . exact hdxs
    . exact hda

theorem insertWith_cons_of_rel {a₁ : α} {b₁ : β a₁} {xs : KVChain r β} {ha₁xs : xs.boundLeft a₁} {a : α} {b : β a} : (ha₁a : r a₁ a) → insertWith f (xs.cons a₁ b₁ ha₁xs) a b = (insertWith f xs a b).cons a₁ b₁ (boundLeft_insertWith_of_boundLeft a₁ ha₁xs ha₁a) := by
  intro ha₁a
  cases xs
  conv => lhs; dsimp [insertWith]; rw [insertWithAux_cons_rel ha₁a]
  apply KVChain.eq_of_toList_eq
  dsimp
  rw [toList_fst_insertWithAux_eq_append]
  rw [toList_snd_insertWithAux_inv]
  dsimp
  rw [List.reverseAux_append_left]
  rfl

theorem insertWith_cons_of_flip {a₁ : α} {b₁ : β a₁} {xs : KVChain r β} {ha₁xs : xs.boundLeft a₁} {a : α} {b : β a} : ∀ (haa₁ : r a a₁), insertWith f (xs.cons a₁ b₁ ha₁xs) a b = (xs.cons a₁ b₁ ha₁xs).cons a b haa₁ := by
  intro haa₁
  unfold insertWith
  rw [insertWithAux_cons_flip haa₁]
  rfl

theorem insertWith_cons_of_eq {xs : KVChain r β} {a : α} {b₁ : β a} {haxs : xs.boundLeft a} {b : β a} : insertWith f (xs.cons a b₁ haxs) a b = (f a b₁ b).casesOn xs (λ bf => xs.cons a bf haxs) := by
  unfold insertWith
  rw [insertWithAux_cons_rfl]
  cases f a b₁ b <;> rfl

end Theorems


/-
## Merge two `KVChain`s 
-/

--- Merge two `KVChain`s with an operation on collision.
def mergeWith (f : (a : α) → β a → β a → Option (β a)) (xs ys : KVChain r β) : KVChain r β :=
  let rec loop : (xs_r : KVChain (flip r) β) → (xs : KVChain r β) → xs_r.hingeable xs → (ys : List (Sigma β)) → ys.Ascending (Sigma.relOnFst r) → ys.predHead (xs_r.boundLeft ∘ Sigma.fst) → KVChain r β
  | xs_r, xs, hxs, [] => λ _ _ => xs_r.hinge xs hxs
  | xs_r, xs, hxs, yys@(y::ys) => λ hascendy hxyys =>
    match xs.toList with
    | [] => xs_r.hinge ⟨yys, (‹yys=_› ▸ hascendy)⟩ $ by
      dsimp [hingeable]
      rw [‹yys=_›, List.relHead_cons_right]
      exact hxyys
    | (_::_) =>
      match hmatch : insertWithAux f xs_r xs hxs y.1 y.2 hxyys with
      | Subtype.mk (xs_r', xs') h =>
          loop xs_r' xs' h ys hascendy.tail $ by
            cases ys
            case nil => exact True.intro
            case cons y₁ ys _ =>
              dsimp [List.predHead]
              have := boundLeft_insertWithAux_fst (r:=r) (β:=β) (f:=f) (xs:=xs_r) (ys:=xs) (hxsys:=hxs) (a:=y.1) (b:=y.2) (haxs:=hxyys) (c:=y₁.1)
              rw [hmatch] at this
              exact this hascendy.head
  loop KVChain.nil xs True.intro ys.toList ys.ascend $ by
    dsimp [boundLeft, List.predHead]
    cases ys.toList <;> exact True.intro


section Theorems

variable {f : (a : α) → β a → β a → Option (β a)}

@[simp]
theorem nil_mergeWith : ∀ (xs : KVChain r β), mergeWith f KVChain.nil xs = xs
| mk xs _ => by
  dsimp [KVChain.nil, mergeWith, mergeWith.loop]
  cases xs <;> rfl

@[simp]
theorem mergeWith_nil : ∀ (xs : KVChain r β), mergeWith f xs KVChain.nil = xs
| mk xs _ => by
  dsimp [KVChain.nil, mergeWith]
  rfl

theorem toList_mergeWith_loop_eq_reverseAux {xs_r : KVChain (flip r) β} {xs : KVChain r β} {hxs : xs_r.hingeable xs} : ∀ {ys : List (Sigma β)} {hascend : ys.Ascending (Sigma.relOnFst r)} {hxsys : ys.predHead (xs_r.boundLeft ∘ Sigma.fst)}, (mergeWith.loop f xs_r xs hxs ys hascend hxsys).toList = List.reverseAux xs_r.toList (mergeWith f xs ⟨ys, hascend⟩).toList := by
  intro ys; revert xs_r xs; induction ys <;> dsimp
  case nil => intros; rfl
  case cons y ys h_ind =>
    intro xs_r xs hxs hascend hyxs
    unfold mergeWith.loop
    revert hxs
    apply xs.recOnList (motive:=λ xs=> ∀ hxs, (mergeWith.loop f xs_r xs hxs (y::ys) hascend hyxs).toList = List.reverseAux xs_r.toList (mergeWith f xs ⟨(y::ys), hascend⟩).toList)
    case nil =>
      intro hxy; rfl
    case cons =>
      intro a b  xs haxs _ hxs
      dsimp [mergeWith.loop]
      rw [h_ind]
      rw [toList_fst_insertWithAux_eq_append]
      rw [toList_snd_insertWithAux_inv]
      rw [List.reverseAux_append_left]
      rw [List.reverseAux_eq_append (as:=xs_r.toList)]
      apply congrArg (xs_r.toList.reverse ++ ·)
      conv =>
        rhs
        unfold mergeWith
        unfold mergeWith.loop
        rw [h_ind]

theorem boundLeft_mergeWith (d : α) {xs ys : KVChain r β} : xs.boundLeft d → ys.boundLeft d → (mergeWith f xs ys).boundLeft d := by
  revert xs
  apply ys.recOnList (motive:=λ ys=> ∀ xs, xs.boundLeft d → ys.boundLeft d → (mergeWith f xs ys).boundLeft d)
  case nil =>
    intros; rw [mergeWith_nil]; assumption
  case cons =>
    intro a₂ b₂ ys ha₂ys h_ind_ys xs hdxs hda₂
    revert h_ind_ys hdxs
    apply xs.recOnList (motive:=λ xs=> (∀ xs₁, xs₁.boundLeft d → ys.boundLeft d → (mergeWith f xs₁ ys).boundLeft d) → xs.boundLeft d → (mergeWith f xs (ys.cons a₂ b₂ ha₂ys)).boundLeft d)
    case nil => rw [nil_mergeWith]; exact λ _ _=> hda₂
    case cons =>
      intro a₁ b₁ xs ha₁xs _ h_ind_ys hda₁
      dsimp [boundLeft, hingeable, mergeWith, mergeWith.loop]
      rw [toList_mergeWith_loop_eq_reverseAux]
      apply dite (r a₁ a₂) <;> intro ha₁a₂
      . rw [insertWithAux_cons_rel ha₁a₂]
        rw [toList_fst_insertWithAux_eq_append]
        rw [List.reverseAux_append_left]
        dsimp [List.reverse, List.reverseAux]
        exact hda₁
      . apply dite (r a₂ a₁) <;> intro ha₂a₁
        . rw [insertWithAux_cons_flip ha₂a₁]
          dsimp [List.reverseAux]
          exact hda₂
        . have : a₂ = a₁ := Trichotomous.eq_of_incomp ⟨ha₂a₁, ha₁a₂⟩
          cases this
          rw [insertWithAux_cons_rfl]
          cases f a₂ b₁ b₂ <;> dsimp
          case none =>
            apply h_ind_ys
            . exact boundLeft_descend (λ _=> trans hda₂) ha₁xs
            . exact boundLeft_descend (λ _=> trans hda₁) ha₂ys
          case some bf =>
            dsimp [List.reverseAux, List.predHead]
            exact hda₂

theorem toList_mergeWith_cons_right {xs : KVChain r β} {a : α} {b : β a} {ys : KVChain r β} {hays : ys.boundLeft a} : (mergeWith f xs (ys.cons a b hays)).toList = List.reverseAux (insertWithAux f KVChain.nil xs True.intro a b True.intro).val.fst (mergeWith f (insertWithAux f KVChain.nil xs True.intro a b True.intro).val.snd ys).toList := by
  apply xs.recOnList (motive:=λ xs=>(mergeWith f xs (ys.cons a b hays)).toList=List.reverseAux (insertWithAux f KVChain.nil xs True.intro a b True.intro).val.fst.toList (mergeWith f (insertWithAux f KVChain.nil xs True.intro a b True.intro).val.snd ys).toList)
  case nil =>
    rw [nil_mergeWith]
    dsimp [List.reverseAux]
    rw [nil_mergeWith]
  case cons =>
    intro a x hax hpa _
    conv =>
      lhs
      unfold mergeWith; unfold mergeWith.loop
      simp
    rw [toList_mergeWith_loop_eq_reverseAux]

theorem cons_mergeWith_rel : ∀ {a : α} {b : β a} {xs : KVChain r β} {haxs : xs.boundLeft a} {ys : KVChain r β}, (hays : ys.boundLeft a) → mergeWith f (xs.cons a b haxs) ys = (mergeWith f xs ys).cons a b (boundLeft_mergeWith a haxs hays) := by
  intro a b xs haxs ys
  revert xs
  apply ys.recOnList (motive:=λ ys => ∀ xs haxs hays, mergeWith f (xs.cons a b haxs) ys = (mergeWith f xs ys).cons a b (boundLeft_mergeWith a haxs hays))
  case nil=> intros; rfl
  case cons =>
    intro b y hby hpb _ x hax hab
    apply KVChain.eq_of_toList_eq
    rw [toList_mergeWith_cons_right]
    rw [KVChain.toList_cons]
    rw [toList_mergeWith_cons_right]
    conv =>
      lhs
      rw [insertWithAux_cons_rel hab]
      rw [toList_fst_insertWithAux_eq_append]
      rw [toList_snd_insertWithAux_inv]
      rw [List.reverseAux_append_left]

theorem mergeWith_cons_flip : ∀ {xs : KVChain r β} {a : α} {b : β a} {ys : KVChain r β} {hays : ys.boundLeft a}, (haxs : xs.boundLeft a) → mergeWith f xs (ys.cons a b hays) = (mergeWith f xs ys).cons a b (boundLeft_mergeWith a haxs hays) := by
  intro xs a b ys hays haxs
  apply KVChain.eq_of_toList_eq
  rw [toList_mergeWith_cons_right]
  suffices (insertWithAux f KVChain.nil xs True.intro a b True.intro).val = (⟨[⟨a,b⟩],List.Ascending.singleton _⟩,xs) by
    rw [this]; rfl
  revert haxs
  apply xs.recOnList (motive:=λ xs=> xs.boundLeft a → (insertWithAux f KVChain.nil xs _ _ _ _).val=_)
  case a.nil => intros; rfl
  case a.cons =>
    intro a₁ b₁ xs ha₁xs _ haa₁
    dsimp [boundLeft, List.predHead] at haa₁
    rw [insertWithAux_cons_flip haa₁]

theorem cons_mergeWith_cons_rel {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} {xs ys : KVChain r β} {ha₁xs : xs.boundLeft a₁} {ha₂ys : ys.boundLeft a₂} : (ha₁a₂ : r a₁ a₂) → mergeWith f (xs.cons a₁ b₁ ha₁xs) (ys.cons a₂ b₂ ha₂ys) = (mergeWith f xs (ys.cons a₂ b₂ ha₂ys)).cons a₁ b₁ (boundLeft_mergeWith a₁ ha₁xs ha₁a₂) :=
  cons_mergeWith_rel (ys:=ys.cons a₂ b₂ ha₂ys)

theorem cons_mergeWith_cons_flip {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} {xs ys : KVChain r β} {ha₁xs : xs.boundLeft a₁} {ha₂ys : ys.boundLeft a₂} : (ha₂a₁ : r a₂ a₁) → mergeWith f (xs.cons a₁ b₁ ha₁xs) (ys.cons a₂ b₂ ha₂ys) = (mergeWith f (xs.cons a₁ b₁ ha₁xs) ys).cons a₂ b₂ (boundLeft_mergeWith a₂ ha₂a₁ ha₂ys) :=
  mergeWith_cons_flip (xs:=xs.cons a₁ b₁ ha₁xs)

theorem cons_mergeWith_cons_rfl {a : α} {b₁ b₂ : β a} {xs ys : KVChain r β} {haxs : xs.boundLeft a} {hays : ys.boundLeft a} : mergeWith f (xs.cons a b₁ haxs) (ys.cons a b₂ hays) = (f a b₁ b₂).casesOn (mergeWith f xs ys) (λ bf => (mergeWith f xs ys).cons a bf (boundLeft_mergeWith a haxs hays)) := by
  apply KVChain.eq_of_toList_eq
  rw [toList_mergeWith_cons_right]
  rw [insertWithAux_cons_rfl]
  cases f a b₁ b₂ <;> rfl

theorem mergeWith_flip {xs ys : KVChain r β} : mergeWith f xs ys = mergeWith (λ a => flip (f a)) ys xs :=
  xs.recOnListOn
    (λ _ => by simp)
    (λ x₁ x₂ xs hxs h_ind_xs ys =>
      ys.recOnListOn
        (by simp)
        (λ y₁ y₂ ys hys h_ind_ys => by
          apply eq_of_toList_eq
          apply dite (r x₁ y₁) <;> intro hx₁y₁
          . rw [cons_mergeWith_cons_rel hx₁y₁]
            rw [cons_mergeWith_cons_flip hx₁y₁]
            dsimp
            rw [h_ind_xs]
          . apply dite (r y₁ x₁) <;> intro hy₁x₁
            . rw [cons_mergeWith_cons_flip hy₁x₁]
              rw [cons_mergeWith_cons_rel hy₁x₁]
              dsimp
              rw [h_ind_ys]
            . have : x₁ = y₁ := Trichotomous.eq_of_incomp ⟨hx₁y₁, hy₁x₁⟩
              cases this
              rw [cons_mergeWith_cons_rfl, cons_mergeWith_cons_rfl]
              dsimp [flip] at *
              cases f x₁ x₂ y₂ <;> dsimp <;> rw [h_ind_xs]
        )
    ) ys

theorem mergeWith_congrFun {f g : (a : α) → β a → β a → Option (β a)} (hfg : ∀ (a : α) (b₁ b₂ : β a), f a b₁ b₂ = g a b₁ b₂) {xs ys : KVChain r β} : mergeWith f xs ys = mergeWith g xs ys :=
  xs.recOnListOn
    (λ _ => by rw [nil_mergeWith, nil_mergeWith])
    (λ x₁ x₂ xs hxs h_ind_xs ys =>
      ys.recOnListOn
        (by rw [mergeWith_nil, mergeWith_nil])
        (λ y₁ y₂ ys hys h_ind_ys => by
          apply eq_of_toList_eq
          apply dite (r x₁ y₁) <;> intro hx₁y₁
          . rw [cons_mergeWith_cons_rel hx₁y₁]
            rw [cons_mergeWith_cons_rel hx₁y₁]
            dsimp
            rw [h_ind_xs]
          apply dite (r y₁ x₁) <;> intro hy₁x₁
          . rw [cons_mergeWith_cons_flip hy₁x₁]
            rw [cons_mergeWith_cons_flip hy₁x₁]
            dsimp
            rw [h_ind_ys]
          have : x₁ = y₁ := Trichotomous.eq_of_incomp ⟨hx₁y₁, hy₁x₁⟩
          cases this
          rw [cons_mergeWith_cons_rfl, cons_mergeWith_cons_rfl]
          dsimp
          rw [hfg]
          cases g x₁ x₂ y₂ <;> dsimp <;> rw [h_ind_xs]
        )
    ) ys

theorem rklex_mergeWith_right {s : (a : α) → β a → β a → Prop} {f : (a : α) → β a → β a → β a} {xs ys zs : KVChain r β} (hsf_right : ∀ a b₁ b, s a b₁ (f a b b₁)) (hsf_stab : ∀ a b₁ b₂ b, s a b₁ b₂ → s a (f a b₁ b) (f a b₂ b)) : KVChain.rklex s xs ys → KVChain.rklex s (xs.mergeWith (λ a b₁ b₂ => some (f a b₁ b₂)) zs) (ys.mergeWith (λ a b₁ b₂ => some (f a b₁ b₂)) zs) :=
  zs.recOnListOn (motive:=λ zs=>∀ xs ys, KVChain.rklex s xs ys → KVChain.rklex s (xs.mergeWith (λ a b₁ b₂ => some (f a b₁ b₂)) zs) (ys.mergeWith (λ a b₁ b₂ => some (f a b₁ b₂)) zs))
    (λ _ _ => by rw [mergeWith_nil]; exact id)
    (λ z₁ z₂ zs hzs h_ind_zs xs ys h =>
      h.recOn
        (λ a b ys hays => by
          have h_ind_zs := h_ind_zs KVChain.nil
          dsimp at *
          rw [nil_mergeWith] at *
          apply dite (r a z₁) <;> intro haz₁
          . rw [cons_mergeWith_cons_rel haz₁]
            exact KVChain.rklex.headFst haz₁
          apply dite (r z₁ a) <;> intro hz₁a
          . rw [cons_mergeWith_cons_flip hz₁a]
            exact KVChain.rklex.tail (h_ind_zs _ KVChain.rklex.nil)
          have : a = z₁ := Trichotomous.eq_of_incomp ⟨haz₁, hz₁a⟩
          cases this
          rw [cons_mergeWith_cons_rfl]
          exact KVChain.rklex.headSnd $ hsf_right _ _ _
        )
        (λ a₁ a₂ b₁ b₂ xs ys haxs hays ha₂a₁=> by
          apply dite (r z₁ a₂) <;> intro hz₁a₂
          . rw [cons_mergeWith_cons_flip hz₁a₂]
            rw [cons_mergeWith_cons_flip (trans hz₁a₂ ha₂a₁)]
            apply KVChain.rklex.tail
            exact h_ind_zs _ _ (KVChain.rklex.headFst ha₂a₁)
          apply dite (r a₂ z₁) <;> intro ha₂z₁
          . rw [cons_mergeWith_cons_rel ha₂z₁]
            apply dite (r z₁ a₁) <;> intro hz₁a₁
            . rw [cons_mergeWith_cons_flip hz₁a₁]
              exact KVChain.rklex.headFst ha₂z₁
            apply dite (r a₁ z₁) <;> intro ha₁z₁
            . rw [cons_mergeWith_cons_rel ha₁z₁]
              exact KVChain.rklex.headFst ha₂a₁
            have : z₁ = a₁ := Trichotomous.eq_of_incomp ⟨hz₁a₁, ha₁z₁⟩
            cases this
            rw [cons_mergeWith_cons_rfl]
            exact KVChain.rklex.headFst ha₂a₁
          have : z₁ = a₂ := Trichotomous.eq_of_incomp ⟨hz₁a₂, ha₂z₁⟩
          cases this
          rw [cons_mergeWith_cons_rfl]
          rw [cons_mergeWith_cons_flip ha₂a₁]
          dsimp
          exact KVChain.rklex.headSnd $ hsf_right _ _ _
        )
        (λ a b₁ b₂ xs ys haxs hays hb₁b₂ => by
          apply dite (r a z₁) <;> intro haz₁
          . rw [cons_mergeWith_cons_rel haz₁]
            rw [cons_mergeWith_cons_rel haz₁]
            exact KVChain.rklex.headSnd hb₁b₂
          apply dite (r z₁ a) <;> intro hz₁a
          . rw [cons_mergeWith_cons_flip hz₁a]
            rw [cons_mergeWith_cons_flip hz₁a]
            apply KVChain.rklex.tail (h_ind_zs _ _ $ KVChain.rklex.headSnd hb₁b₂)
          have : a = z₁ := Trichotomous.eq_of_incomp ⟨haz₁, hz₁a⟩
          cases this
          rw [cons_mergeWith_cons_rfl]
          rw [cons_mergeWith_cons_rfl]
          dsimp
          exact KVChain.rklex.headSnd $ hsf_stab _ _ _ _ hb₁b₂
        )
        (λ a b xs ys haxs hays htail h_ind => by
          apply dite (r a z₁) <;> intro haz₁
          . rw [cons_mergeWith_cons_rel haz₁]
            rw [cons_mergeWith_cons_rel haz₁]
            exact KVChain.rklex.tail h_ind
          apply dite (r z₁ a) <;> intro hz₁a
          . rw [cons_mergeWith_cons_flip hz₁a]
            rw [cons_mergeWith_cons_flip hz₁a]
            exact KVChain.rklex.tail (h_ind_zs _ _ $ KVChain.rklex.tail htail)
          have : a = z₁ := Trichotomous.eq_of_incomp ⟨haz₁, hz₁a⟩
          cases this
          rw [cons_mergeWith_cons_rfl]
          rw [cons_mergeWith_cons_rfl]
          exact KVChain.rklex.tail (h_ind_zs _ _ htail)
        )
    )
    xs ys

end Theorems

end KVChain
