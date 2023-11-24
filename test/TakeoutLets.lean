import Std.Tactic.Basic
import Std.Tactic.GuardExpr
import Algdata.Tactic.TakeoutLets

def nestedLetFun : Nat :=
  let j := 1
  have hj : j = 1 := rfl
  have : True := by
    have : True := .intro
    exact .intro
  (⟨j,hj⟩ : Subtype (·=1)).1

example : nestedLetFun = 1 := by
  unfold nestedLetFun
  takeout_lets
  let j := 1
  iterate intro_let
  guard_hyp hj : j = 1
  guard_hyp this : True
  guard_target = (Subtype.mk j hj).1 = 1
  rfl

example : ∀ (i : Fin nestedLetFun), i.1+1 = nestedLetFun := by
  unfold nestedLetFun
  takeout_lets; repeat intro_let
  /-
  j : Nat := 1
  hj : j = 1
  this : True
  ⊢ ∀ (i : Fin { val := j, property := hj }.val),
    i.val + 1 =
      let j := 1;
      let_fun hj := (_ : j = j);
      let_fun this := (_ : True);
      { val := j, property := hj }.val
  -/
  guard_hyp hj : j = 1
  guard_hyp this : True
  intro i
  takeout_lets; iterate intro_let
  /-
  j : Nat := 1
  hj : j = 1
  this : True
  i : Fin { val := j, property := hj }.val
  ⊢ i.val + 1 = { val := j, property := hj }.val
  -/
  guard_hyp hj : j = 1
  guard_hyp this : True
  guard_target = i.val +1 = (Subtype.mk j hj).val
  dsimp at i ⊢; have ⟨i,hi⟩ := i
  cases hi; rfl; contradiction

def wfLetFun (n : Nat) : Nat :=
  let i := if n % 2 = 0 then n / 2 else n-1
  have : True := .intro
  if hn : n > 0 then
    have : i < n := by
      if h : n % 2 = 0 then
        dsimp; rewrite [if_pos h]; exact n.div_lt_self hn .refl
      else
        dsimp; rewrite [if_neg h]; exact n.sub_lt hn .refl
    wfLetFun i + 1
  else
    0

example (n : Nat) : wfLetFun n = wfLetFun n := by
  unfold wfLetFun
  takeout_lets; iterate intro_let
  if hn : n > 0 then
    rewrite [dif_pos hn]
    takeout_lets; iterate intro_let
    rfl
  else
    rewrite [dif_neg hn]
    rfl
