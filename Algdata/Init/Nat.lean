/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Logic
import Std.Data.Nat.Lemmas

import Algdata.Tactic.PkgLocal

namespace Nat

@[pkg_local]
private theorem min_zero' (n : Nat) : min n 0 = 0 := by
  rw [Nat.min_def]
  if h : n ≤ 0
  then cases h; exact if_pos Nat.le.refl
  else exact if_neg h

@[pkg_local]
private theorem min_eq_right' {m n : Nat} (h : m ≥ n) : min m n = n := by
  rw [Nat.min_def]
  if hmn : m ≤ n then
    have : m = n := Nat.le_antisymm hmn h
    rw [if_pos hmn, this]
  else
    rw [if_neg hmn]

@[pkg_local]
private theorem min_succ_succ' (m n : Nat) : min m.succ n.succ = (min m n).succ := by
  if h : m ≤ n then
    rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.succ_le_succ h)]
  else
    have : m ≥ n := Nat.le_of_lt (Nat.gt_of_not_le h)
    rw [Nat.min_eq_right' this, Nat.min_eq_right' (Nat.succ_le_succ this)]

@[pkg_local]
private theorem min_eq (n : Nat) : min n n = n :=
  Nat.min_eq_left n.le_refl

@[pkg_local]
private theorem add_sub_assoc' {m k : Nat} : m ≤ k → ∀ (n : Nat), n + m - k = n - (k - m) := by
  intro hmk n
  have : k = (k-m) + m := Eq.symm $ Nat.sub_add_cancel hmk
  conv => lhs; rw [this, Nat.add_sub_add_right]

@[pkg_local]
private theorem add_pred {m n : Nat} : n > 0 → m + n.pred = (m+n).pred := by
  intro hn
  cases n
  case zero =>
    exact (zero.not_lt_zero hn).elim
  case succ n =>
    simp [Nat.add_succ]

@[pkg_local]
private theorem lt_of_mul_lt_mul_left {a b c : Nat} : a*b < a*c → b < c := by
  intro h
  apply Nat.lt_of_not_le; intro hcontra
  have := Nat.mul_le_mul_left a hcontra
  exact absurd h (Nat.not_lt_of_le this)

@[pkg_local]
private theorem lt_of_mul_lt_mul_right {a b c : Nat} : a*c < b*c → a < b := by
  intro h
  apply Nat.lt_of_not_le; intro hcontra
  have := Nat.mul_le_mul_right c hcontra
  exact absurd h (Nat.not_lt_of_le this)

@[pkg_local]
private theorem eq_zero_of_lt_one : ∀ {n : Nat}, n < 1 → n = 0
| 0, _ => rfl

@[pkg_local]
private theorem div_le_div {a b c : Nat} : a ≤ b → a/c ≤ b/c := by
  intro hab
  cases Nat.lt_or_ge (b/c) (a/c)
  case inr hge => exact hge
  case inl hlt =>
    have : c > 0 := (Nat.lt_or_ge 0 c).elim id $ by
      intro h; cases h; rw [Nat.div_zero, Nat.div_zero] at hlt; cases hlt
    have := (Nat.div_lt_iff_lt_mul ‹c>0›).mp hlt
    have := calc
      b < a/c*c := this
      _ ≤ a := Nat.div_mul_le_self a c
      _ ≤ b := hab
    exact absurd this (Nat.lt_irrefl b)

@[pkg_local]
private theorem mul_add_div_left (y z : Nat) {x : Nat} : x > 0 → (x*y + z)/x = y + z/x := by
  intro h; rw [Nat.add_comm, Nat.add_mul_div_left z y h, Nat.add_comm]

@[pkg_local]
private theorem mul_add_div_right (x z : Nat) {y : Nat} : y > 0 → (x*y + z)/y = x + z/y := by
  intro h; rw [Nat.add_comm, Nat.add_mul_div_right z x h, Nat.add_comm]

@[pkg_local]
private theorem mod_mul_mod (a b n : Nat) : a % n * b % n = (a*b)%n :=
  Eq.symm $ calc
    a * b % n = (n*(a/n) + a % n) * b % n := by conv => lhs; rw [←Nat.div_add_mod a n]
    _         = (n * (a/n * b) + a % n * b) % n := by rw [Nat.right_distrib, Nat.mul_assoc]
    _         = a % n * b % n := by rw [Nat.add_comm,Nat.add_mul_mod_self_left]

@[pkg_local]
private theorem mod_mod_le (a : Nat) {m n : Nat} : m > 0 → m ≤ n → a % m % n = a % m := by
  intro hm hle
  have : a % m < n := Trans.trans (Nat.mod_lt a hm) hle
  rw [Nat.mod_eq_of_lt this]

@[pkg_local]
private theorem mod_mul_mod_left (a m n : Nat) : a % (m*n) % m = a % m := by
  conv =>
    rhs;
    rw [←Nat.div_add_mod a (m*n), Nat.add_comm, Nat.mul_assoc]
    simp

@[pkg_local]
private theorem mod_mul_mod_right (a m n : Nat) : a % (m*n) % n = a % n := by
  rw [Nat.mul_comm, mod_mul_mod_left]

@[pkg_local]
private theorem mod_mul_div_left (l m n : Nat) : (l % (m*n) / m) = (l/m) % n := by
  cases m.eq_zero_or_pos
  case inl hm =>
    cases hm; simp
  case inr hm =>
  cases n.eq_zero_or_pos
  case inl hn =>
    cases hn; simp [Nat.mod_zero]
  case inr hn =>
    conv =>
      rhs;
      rw [←Nat.div_add_mod l (m*n)]
      rw [Nat.add_comm, Nat.mul_assoc, Nat.add_mul_div_left _ _ hm]
      rw [Nat.add_mul_mod_self_left]
    apply (Nat.mod_eq_of_lt ?_).symm
    apply (div_lt_iff_lt_mul hm).mpr
    rw [Nat.mul_comm]
    exact Nat.mod_lt l (Nat.mul_pos hn hm)

@[pkg_local]
private theorem mod_mul_div_right (l m n : Nat) : (l % (m*n) / n) = (l/n) % m := by
  rw [Nat.mul_comm, mod_mul_div_left]

@[pkg_local]
private theorem mul_sub_mod_left {l m n : Nat} : m > 0 → l ≥ n → (l*m - n)%l = (l-n)%l := by
  intro hm hln
  cases hm
  case refl => rw [Nat.mul_one]
  case step _ _ =>
    rw [mul_succ, Nat.add_sub_assoc hln, Nat.add_comm, Nat.add_mul_mod_self_left]

@[pkg_local]
private theorem mul_sub_mod_right {l m n : Nat} : l > 0 → m ≥ n → (l*m - n)%m = (m-n)%m := by
  intro hl hmn; rw [Nat.mul_comm, mul_sub_mod_left hl hmn]


/-!
## Power opertor
-/

@[pkg_local]
private theorem exp_lt_pow {n : Nat} (i : Nat) : n ≥ 2 → i < n^i := by
  intro h
  induction i
  case zero => exact Nat.le.refl
  case succ i h_ind =>
  have : n^i > 0 := Nat.pos_pow_of_pos i (Nat.lt_of_succ_lt h)
  calc
    i+1 < n^i + 1 := succ_lt_succ h_ind
    _   ≤ n^i + n^i := Nat.add_le_add_left this _
    _   = n^i*2 := (Nat.mul_two _).symm
    _   ≤ n^i*n := Nat.mul_le_mul_left _ h
    _   = n^(i+1) := rfl

@[pkg_local]
private theorem pow_lt_pow_right {n i j : Nat} : n ≥ 2 → i < j → n^i < n^j := by
  intro hn hij
  induction hij
  case refl => calc
    n^i < n^i + n^i := Nat.lt_add_of_pos_left (Nat.pos_pow_of_pos i (trans (Nat.zero_lt_succ 1) hn))
    _   = n^i*2 := (Nat.mul_two _).symm
    _   ≤ n^i*n := Nat.mul_le_mul_left (n^i) hn
  case step j _ h_ind => calc
    n^i < n^j := h_ind
    _   ≤ n^j + n^j := Nat.le_add_left _ _
    _   = n^j*2 := (Nat.mul_two _).symm
    _   ≤ n^j*n := Nat.mul_le_mul_left _ hn

@[pkg_local]
private theorem pow_lt_pow_left {m n i : Nat} : m < n → i > 0 → m^i < n^i := by
  intro hmn hi
  cases i
  case zero => cases hi
  case succ i => calc
    m^i.succ = m^i * m := rfl
    _        ≤ n^i * m := Nat.mul_le_mul_right m (Nat.pow_le_pow_of_le_left (Nat.le_of_lt hmn) i)
    _        < n^i * n := Nat.mul_lt_mul_of_pos_left hmn (Nat.pos_pow_of_pos i (trans m.zero_le hmn))


/-!
## Ordering
-/
@[pkg_local]
private theorem compare_lt {m n : Nat} : m < n → compare m n = Ordering.lt := by
  intro h
  simp [compare, instOrdNat, compareOfLessAndEq]
  rw [if_pos h]

@[pkg_local]
private theorem compare_eq {m n : Nat} : m = n → compare m n = Ordering.eq := by
  intro h; cases h
  simp [compare, instOrdNat, compareOfLessAndEq]

@[pkg_local]
private theorem compare_gt {m n : Nat} : m > n → compare m n = Ordering.gt := by
  intro h
  simp [compare, instOrdNat, compareOfLessAndEq]
  rw [if_neg (Nat.lt_asymm h), if_neg (Nat.ne_of_lt h).symm]


/-!
## Decidability of quantifiers
-/

@[pkg_local]
private theorem exists_or_forall_not (p : Nat → Prop) [DecidablePred p] (n : Nat) : (∃ i, (i < n ∧ p i)) ∨ (∀ i, i < n → ¬ p i) := by
  induction n
  case zero => exact Or.inr (λ _ h => by cases h)
  case succ n h_ind =>
    cases h_ind
    case inl hex =>
      cases hex with | intro i hi => exact Or.inl ⟨i, Nat.le.step hi.left, hi.right⟩
    case inr hall =>
      if hpn : p n
      then exact Or.inl ⟨n, n.lt_succ_self, hpn⟩
      else
        apply Or.inr
        intro i hi
        cases hi
        case refl => exact hpn
        case step hstep => exact hall i hstep


/-!
## folding
-/

@[pkg_local]
private theorem foldM_zero {m : Type u → Type v} [Monad m] {α : Type u} {f : Nat → α → m α} {init : α} : foldM f init 0 = pure init := rfl

@[pkg_local]
private theorem foldM_succ {m : Type u → Type v} [Monad m] {α : Type u} {f : Nat → α → m α} {init : α} {n : Nat} : foldM f init (n+1) = f 0 init >>= λ x => foldM (f ∘ Nat.succ) x n := by
  unfold foldM
  conv =>
    lhs; unfold foldM.loop
    simp only [Nat.add_eq, Nat.add_zero, Nat.add_sub_cancel_left, Nat.sub_self]
  suffices ∀ k, k ≤ n → foldM.loop f (n+1) k = foldM.loop (f ∘ succ) n k
    by rw [this n .refl]
  intro k hk
  induction k
  case zero => rfl
  case succ k h_ind =>
    dsimp [foldM.loop]
    have := calc
      n+1-k-1 = n.succ - k.succ := by simp only [Nat.sub_sub]
      _       = n-k := Nat.succ_sub_succ ..
    have := calc
      succ (n-k-1) = n-k-1+1 := rfl
      _            = n-k := Nat.sub_add_cancel (Nat.lt_sub_of_add_lt (Nat.zero_add .. ▸ hk))
    rw [‹n+1-k-1=n-k›, ‹succ (n-k-1)=n-k›]
    rw [h_ind (Nat.le_of_succ_le hk)]

@[pkg_local]
private theorem foldM_succ_eq_foldM_bind {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u} {f : Nat → α → m α} {init : α} {n : Nat} : foldM f init (n+1) = foldM f init n >>= f n := by
  induction n generalizing f init
  case zero =>
    conv =>
      dsimp [foldM, foldM.loop]
      change f 0 init >>= pure = pure init >>= f 0
    simp only [pure_bind, bind_pure]
  case succ n h_ind =>
    simp only [Nat.succ_eq_add_one]
    conv => lhs; rw [foldM_succ]; rhs; ext; rw [h_ind]
    conv => rhs; rw [foldM_succ]
    dsimp; rw [bind_assoc]

@[pkg_local]
private theorem fold_eq_foldM {α : Type u} {f : Nat → α → α} {init : α} {n : Nat} : fold f n init = foldM (m:=Id) f init n := by
  induction n
  case zero => rfl
  case succ n h_ind =>
    rw [foldM_succ_eq_foldM_bind, ←h_ind]; rfl

@[pkg_local]
private theorem fold_hom {α : Type u} {β : Type v} (f : α → β) (g₁ : Nat → α → α) (g₂ : Nat → β → β) (n : Nat) (init : α) (hf : ∀ (i : Nat) (a : α), i < n → g₂ i (f a) = f (g₁ i a)) : n.fold g₂ (f init) = f (n.fold g₁ init) :=
  hf |> n.rec (λ _ => rfl) λ n IH hf => by
    dsimp [Nat.fold]
    have IH := IH λ i a h => hf i a (trans h n.lt_succ_self)
    rw [IH, hf n _ n.lt_succ_self]

@[pkg_local]
private theorem fold_congr {α : Type u} (f g : Nat → α → α) (n : Nat) (init : α) (zero : f 0 init = g 0 init) (succ : ∀ (i : Nat) (a : α), (i+1 < n) → f (i+1) (g i a) = g (i+1) (g i a)) : n.fold f init = n.fold g init :=
  succ |> n.rec (λ _ => rfl) fun
    | 0, _, _ => zero
    | n+1, IH, hsucc =>
      Eq.trans
        (congrArg (f (n+1)) (IH λ _ _ h => hsucc _ _ (trans h (n+1).lt_succ_self)))
        (hsucc n _ (n+1).lt_succ_self)

@[pkg_local]
private theorem foldRev_succ (f : Nat → α → α) (n : Nat) (init : α) : (n+1).foldRev f init = f 0 (n.foldRev (f ∘ succ) init) := by
  induction n generalizing f init with
  | zero => rfl
  | succ n IH =>
    unfold foldRev; simp only [Nat.add, Nat.succ_eq_add_one]
    rewrite [IH]; rfl

@[pkg_local]
private theorem foldRev_induction {motive : Nat → α → Prop}
    (f : Nat → α → α) (n : Nat) (init : α)
    (hinit : motive n init)
    (hsucc : ∀ (k : Nat) (a : α), motive (k+1) a → motive k (f k a)) :
    (motive 0 (n.foldRev f init)) := by
  induction n generalizing f init motive with
  | zero => exact hinit
  | succ n IH =>
    rewrite [foldRev_succ]
    apply hsucc
    exact @IH (motive ∘ succ) (f ∘ succ) init hinit (fun k => hsucc (k+1))


/-!
## Bit operations
-/

@[pkg_local]
private theorem shiftRight_one (n : Nat) : n >>> 1 = n/2 := rfl

@[pkg_local]
private theorem shiftRight_le_self (n k : Nat) : n >>> k ≤ n := by
  induction k
  case zero => exact Nat.le.refl
  case succ k h_ind=>
    conv => lhs; change (n >>> k) / 2
    calc
      (n >>> k) / 2 ≤ n >>> k := Nat.div_le_self _ 2
      _             ≤ n := h_ind

@[pkg_local]
private theorem shiftRight_lt {n k : Nat} : n ≠ 0 → k > 0 → n.shiftRight k < n := by
  intro hn hk
  induction k
  case zero => exact absurd hk (Nat.lt_irrefl 0)
  case succ k h_ind =>
    unfold shiftRight
    cases Nat.eq_zero_or_pos k
    case inl h =>
      cases h; dsimp [shiftRight]
      exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (Nat.lt_succ_self 1)
    case inr h =>
      calc
        shiftRight n k / 2
          ≤ shiftRight n k := Nat.div_le_self _ _
        _ < n := h_ind h

end Nat
