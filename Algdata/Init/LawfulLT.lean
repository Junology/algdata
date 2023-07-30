/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic

import Algdata.Init.Order

section LawfulLE

/-
  `LE` with the axioms of pre-orderings
-/
class LawfulLE (α : Type _) extends LE α where
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

instance (α : Type _) [LawfulLE α] : Trans (α:=α) (β:=α) (γ:=α) (·≤·) (·≤·) (·≤·) where
  trans := LawfulLE.trans

instance instLawfulLENat : LawfulLE Nat where
  refl := Nat.le_refl
  trans := Nat.le_trans

end LawfulLE


section LawfulLT

/-!
  `LT` with the axioms of strict partial orderings
-/
class LawfulLT (α : Type _) extends LT α, Trans (α:=α) (β:=α) (γ:=α) LT.lt LT.lt LT.lt, Irreflective (α:=α) LT.lt where

attribute [instance] LawfulLT.mk

instance instLawfulLTProd (α β : Type _) [LawfulLT α] [LawfulLT β] : LawfulLT (α × β) where
  lt := Prod.lexLt
  irrefl := by
    intro (a,b); simp [LT.lt]
    apply not_or.mpr
    constructor
    case left => exact Irreflective.irrefl _
    case right => intro h; exact Irreflective.irrefl b h.right
  trans := by
    intro (a₁,a₂) (b₁,b₂) (c₁,c₂); simp [LT.lt]
    intro hab hbc
    cases hab
    case inl hab1 =>
      cases hbc
      case inl hbc1 =>
        exact Or.inl $ calc
          a₁ < b₁ := hab1
          _  < c₁ := hbc1
      case inr hbc2 =>
        cases hbc2.1; exact Or.inl hab1
    case inr hab2 =>
      cases hab2.1
      cases hbc
      case inl hbc1 => exact Or.inl hbc1
      case inr hbc2 =>
        cases hbc2.1
        exact Or.inr $ And.intro rfl $ calc
          a₂ < b₂ := hab2.2
          _  < c₂ := hbc2.2


namespace LawfulLT

variable {α : Type _} [LawfulLT α]

theorem eq_or_lt_trans {a b c : α} : a = b ∨ a < b → b = c ∨ b < c → a = c ∨ a < c := by
  intro hab hbc
  cases hab
  case inl haeqb => cases haeqb; exact hbc
  case inr haltb =>
    apply Or.inr
    cases hbc
    case inl hbeqc => cases hbeqc; exact haltb
    case inr hbltc => exact trans haltb hbltc

theorem lt_of_eq_or_lt_of_lt {a b c : α} : a = b ∨ a < b → b < c → a < c := by
  intro hab hbc
  cases hab
  case inl h => cases h; exact hbc
  case inr h => exact trans h hbc

theorem lt_of_lt_of_eq_or_lt {a b c : α} : a < b → b = c ∨ b < c → a < c := by
  intro hab hbc
  cases hbc
  case inl h => cases h; exact hab
  case inr h => exact trans hab h

end /- namespace -/ LawfulLT

end /- section -/ LawfulLT


section ConnectedLT

/-
  `LT` such that `x ≲ y := ¬ y < x` defines a total preordering compatible with the original strict ordering.
-/
class ConnectedLT (α : Type _) extends LawfulLT α where
  not_gt_trans : ∀ {a b c : α}, ¬ a > b → ¬ b > c → ¬ a > c
  lt_of_lt_of_not_gt : ∀ {a b c : α}, a < b → ¬ b > c → a < c
  lt_of_not_gt_of_lt : ∀ {a b c : α}, ¬ a > b → b < c → a < c

protected
def ConnectedLT.qle {α : Type _} [ConnectedLT α] : α → α → Prop :=
  λ a b => ¬ a > b

@[reducible]
protected
def ConnectedLT.qge {α : Type _} [ConnectedLT α] : α → α → Prop :=
  λ a b => ConnectedLT.qle b a

protected
def ConnectedLT.Equiv {α : Type _} [ConnectedLT α] : α → α → Prop :=
  λ a b => ConnectedLT.qle a b ∧ ConnectedLT.qge a b

infix:50 " ≲ " => ConnectedLT.qle
infix:50 " ≳ " => ConnectedLT.qge

instance (α : Type _) [ConnectedLT α] : HasEquiv α where
  Equiv := ConnectedLT.Equiv

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·≲·) (·<·) (·<·) where
  trans := ConnectedLT.lt_of_not_gt_of_lt

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·<·) (·≲·) (·<·) where
  trans := ConnectedLT.lt_of_lt_of_not_gt

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·≈·) (·<·) (·<·) where
  trans hab hbc := trans hab.left hbc

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·<·) (·≈·) (·<·) where
  trans hab hbc := trans hab hbc.left

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·≲·) (·≲·) (·≲·) where
  trans := ConnectedLT.not_gt_trans

instance (α : Type _) [ConnectedLT α] : Trans (α:=α) (·≈·) (·≈·) (·≈·) where
  trans hab hbc := by
    simp [HasEquiv.Equiv, ConnectedLT.Equiv, ConnectedLT.qge] at *
    apply And.intro
    case left => exact trans hab.left hbc.left
    case right => exact trans hbc.right hab.right

namespace ConnectedLT

variable {α : Type _} [ConnectedLT α]

theorem qle_of_lt {a b : α} : a < b → a ≲ b := Asymmetry.asymm _ _
theorem qge_of_gt {a b : α} : a > b → a ≳ b := Asymmetry.asymm (r:=LT.lt) _ _

theorem equiv_refl (a : α) : a ≈ a :=
  And.intro (Irreflective.irrefl (r:=LT.lt) a) (Irreflective.irrefl (r:=LT.lt) a)

theorem equiv_symm {a b : α} : a ≈ b → b ≈ a := And.comm.mp

protected
theorem subst {a₁ a₂ b₁ b₂ : α} : a₁ ≈ a₂ → b₁ ≈ b₂ → a₁ < b₁ → a₂ < b₂ := by
  intro ha hb h₁
  apply ConnectedLT.lt_of_lt_of_not_gt _ hb.left
  apply ConnectedLT.lt_of_not_gt_of_lt ha.right h₁

protected
theorem subst_right {a b₁ b₂ : α} : b₁ ≈ b₂ → a < b₁ → a < b₂ :=
  ConnectedLT.subst (equiv_refl _)

protected
theorem subst_left {a₁ a₂ b : α} : a₁ ≈ a₂ → a₁ < b → a₂ < b :=
  flip ConnectedLT.subst (equiv_refl _)

end /-namespace-/ ConnectedLT

end ConnectedLT


section LinearLT

/-
  `LT` of strict linear orderings
-/
class LinearLT (α : Type _) extends LawfulLT α, Trichotomous (α:=α) LT.lt where

namespace LinearLT

variable {α : Type _} [LinearLT α]

example : StrictLinearOrder (α:=α) (r:=LT.lt) := inferInstance
example : Asymmetry (α:=α) (r:=LT.lt) := inferInstance

theorem not_lt_iff_eq_or_gt {a b : α} : ¬ a < b ↔ (a = b ∨ a > b) where
  mp := by
    apply trichotCases (r:=LT.lt) (motive:=λ a b => ¬ a < b → a=b ∨ a > b)
    case of_rfl => exact λ _ _ => Or.inl rfl
    case of_rel => exact λ _ _ => absurd
    case of_opp => exact λ _ _ h _ => Or.inr h
  mpr := by
    intro hor hlt
    cases hor
    case inl heq => cases heq; exact Irreflective.irrefl _ hlt
    case inr hgt => exact Asymmetry.asymm _ _ hlt hgt

theorem not_gt_iff_eq_or_lt {a b : α} : ¬ a > b ↔ (a = b ∨ a < b) where
  mp hngt := Or.imp_left Eq.symm $ not_lt_iff_eq_or_gt.mp hngt
  mpr hor := not_lt_iff_eq_or_gt.mpr $ hor.imp_left Eq.symm

theorem not_eq_iff_lt_or_gt {a b : α} : a ≠ b ↔ (a < b ∨ a > b) where
  mp :=
    trichotCasesOn (r:=LT.lt) (motive:=λ a b => a ≠ b → a < b ∨ a > b) a b (λ _ hneq => absurd rfl hneq) (λ _ _ h _ => Or.inl h) (λ _ _ h _ => Or.inr h)
  mpr hor := by
    intro heq; cases heq
    cases hor
    case inl h => exact LinearLT.toLawfulLT.irrefl _ h
    case inr h => exact LinearLT.toLawfulLT.irrefl _ h

end /- namespace -/ LinearLT

instance instLinearLTPUnit : LinearLT PUnit where
  lt _ _ := False
  irrefl _ := id
  trans _ := id
  trichot | (), () => Or.inl rfl

instance instLinearLTNat : LinearLT Nat where
  irrefl := Nat.lt_irrefl
  trans := Nat.lt_trans
  trichot := Trichotomous.trichot (r:=Nat.lt)

instance instLinearLTFin (n : Nat) : LinearLT (Fin n) where
  irrefl x := Nat.lt_irrefl x.val
  trans := Nat.lt_trans
  trichot x y := by
    apply Or.imp_left Fin.eq_of_val_eq
    exact Trichotomous.trichot (r:=LT.lt) x.val y.val

instance instLinearLTUTF32 : LinearLT UInt32 where
  irrefl x := Nat.lt_irrefl x.val.val
  trans := Nat.lt_trans
  trichot x y  := by
    have : {x y : UInt32} → x.val = y.val → x=y := by
      intro x y hxy
      cases x; cases y; cases hxy; rfl
    apply Or.imp_left this
    exact Trichotomous.trichot (r:=LT.lt) x.val y.val

instance instLinearLTChar : LinearLT Char where
  irrefl c := Nat.lt_irrefl c.val.val.val
  trans := Nat.lt_trans
  trichot x y := by
    have : {x y : Char} → x.val = y.val → x=y := by
      intro x y hxy
      cases x; cases y; cases hxy; rfl
    apply Or.imp_left this
    exact Trichotomous.trichot (r:=LT.lt) x.val y.val

instance instLinearLTProd (α β : Type _) [LinearLT α] [LinearLT β] : LinearLT (α × β) where
  trichot := by
    intro (a₁,b₁) (a₂,b₂)
    apply trichotCasesOn (motive:=λ x y => (x,b₁) = (y,b₂) ∨ (x,b₁) < (y,b₂) ∨ (x,b₁) > (y,b₂)) LT.lt a₁ a₂
    case of_rfl =>
      intro a
      apply trichotCasesOn (motive:=λ x y => (a,x) = (a,y) ∨ (a,x) < (a,y) ∨ (a,x) > (a,y)) LT.lt b₁ b₂
      case of_rfl => intros; exact Or.inl rfl
      case of_rel => intro _ _; exact Or.inr ∘ Or.inl ∘ Or.inr ∘ And.intro rfl
      case of_opp => intro _ _; exact Or.inr ∘ Or.inr ∘ Or.inr ∘ And.intro rfl
    case of_rel => intro _ _; exact Or.inr ∘ Or.inl ∘ Or.inl
    case of_opp => intro _ _; exact Or.inr ∘ Or.inr ∘ Or.inl

instance instLinearLTList {α : Type _} [LinearLT α] : LinearLT (List α) where
  irrefl := by
    intro x hlt; induction x
    case nil => cases hlt
    case cons a as h_ind =>
      cases hlt
      case head h => exact Irreflective.irrefl a h
      case tail h => exact h_ind h
  trans := by
    intro x; induction x<;> intro y z hxy hyz
    case nil =>  cases hyz <;> exact List.lt.nil _ _
    case cons a as h_ind =>
      cases y; case nil => cases hxy
      case cons b bs =>
      cases z; case nil => cases hyz
      case cons c cs =>
      cases hxy
      case head hab =>
        apply List.lt.head
        cases hyz
        case a.head hbc => exact trans hab hbc
        case a.tail hab hbc hcb htail =>
          have := Trichotomous.eq_of_incomp ⟨hbc,hcb⟩
          exact this ▸ hab
      case tail hab hba htail =>
        have := Trichotomous.eq_of_incomp ⟨hab,hba⟩
        cases this
        cases hyz
        case head hac => exact List.lt.head _ _ hac
        case tail hac hca htail =>
          apply List.lt.tail hac hca
          exact h_ind ‹as < bs› htail
  trichot := by
    intro x; induction x <;> intro y
    case nil =>
      cases y
      case nil => exact Or.inl rfl
      case cons b bs => exact Or.inr (Or.inl (List.lt.nil _ _))
    case cons a as h_ind =>
      cases y
      case nil => exact Or.inr (Or.inr (List.lt.nil _ _))
      case cons b bs =>
        cases Trichotomous.trichot (r:=LT.lt) a b
        case inl heq =>
          cases heq
          apply Or.imp (congrArg (List.cons a)) (Or.imp (List.lt.tail (Irreflective.irrefl a) (Irreflective.irrefl a)) (List.lt.tail (Irreflective.irrefl a) (Irreflective.irrefl a)))
          exact h_ind bs
        case inr h =>
          cases h
          case inl hab => exact Or.inr (Or.inl (List.lt.head _ _ hab))
          case inr hba => exact Or.inr (Or.inr (List.lt.head _ _ hba))

instance instLinearLTString : LinearLT String where
  irrefl x := by cases x with | mk cs => exact Irreflective.irrefl (α:=List Char) (r:=LT.lt) cs
  trans {x} {y} {z} hxy hyz :=
    by cases x; cases y; cases z; exact Trans.trans (r:=LT.lt (α:=List Char)) (s:=LT.lt (α:=List Char)) hxy hyz
  trichot x y :=
    by cases x with | mk xs => cases y with | mk ys =>
    have : xs = ys → String.mk xs = String.mk ys := λ h => by cases h; rfl
    apply Or.imp_left this
    exact Trichotomous.trichot (r:=LT.lt (α:=List Char)) xs ys

instance instConnectedLTLinearLT (α : Type _) [LinearLT α] : ConnectedLT α where
  not_gt_trans := by
    intro a b c hab hbc
    apply LinearLT.not_gt_iff_eq_or_lt.mpr
    have hab := LinearLT.not_gt_iff_eq_or_lt.mp hab
    have hbc := LinearLT.not_gt_iff_eq_or_lt.mp hbc
    exact LawfulLT.eq_or_lt_trans hab hbc
  lt_of_not_gt_of_lt := by
    intro a b c hab hbc
    have := LinearLT.not_gt_iff_eq_or_lt.mp hab
    exact LawfulLT.lt_of_eq_or_lt_of_lt this hbc
  lt_of_lt_of_not_gt := by
    intro a b c hab hbc
    have := LinearLT.not_gt_iff_eq_or_lt.mp hbc
    exact LawfulLT.lt_of_lt_of_eq_or_lt hab this

end LinearLT
