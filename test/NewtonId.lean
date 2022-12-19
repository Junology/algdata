/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Algebra.Polynomial.Polynomial
import Algdata.Data.Nat.Pow

inductive Vars : Type
| X : Vars
| Y : Vars
| Z : Vars
  deriving DecidableEq

instance : Repr Vars where
  reprPrec x _ := match x with | Vars.X => "X" | Vars.Y => "Y" | Vars.Z => "Z"

instance instLinearLTVars : LinearLT Vars where
  lt x y := match x, y with
    | Vars.X, Vars.Y => True
    | Vars.X, Vars.Z => True
    | Vars.Y, Vars.Z => True
    | _, _ => False
  trans {x} {y} {z} hxy hyz := by
    cases x <;> cases y <;> cases z <;> try {exact False.elim hxy} <;> try {exact False.elim hyz} <;> try {exact True.intro}
  irrefl x := by cases x <;> exact not_false
  trichot x y := by cases x <;> cases y <;> simp

instance instDecidableRelLTVars : DecidableRel (r:=LT.lt (α:=Vars)) := by
  intro x y
  cases x <;> cases y <;> try {exact isTrue (True.intro)} <;> try {exact isFalse not_false}

#print axioms instLinearLTVars

open Vars

#eval 3⊙[(X,2), (Y,4)]⊙[('A',3)] + 4⊙[(X,1)]⊙[('B',1)] + 1 + 0 + 4⊙[(X,2),(Y,4)]⊙[('B',3)]

#eval Nat.gpow  (3⊙[(X,1),(Z,1)] + 2⊙[(Y,2)] + 1⊙[(Y,1),(Z,1)]) 10
#eval Nat.sqPow (3⊙[(X,1),(Z,1)] + 2⊙[(Y,2)] + 1⊙[(Y,1),(Z,1)]) 10


def powpoly : Nat → Polynomial Int String MonomialOrder.deglex
| 0 => 3
| 1 => 1⊙[("e₁", 1)]
| 2 => 1⊙[("e₁",2)] + (-2)⊙[("e₂",1)]
| (n+3) => 1⊙[("e₁",1)] * powpoly (n+2) + (-1)⊙[("e₂",1)] * powpoly (n+1) + 1⊙[("e₃",1)] * powpoly n

#eval powpoly 5
#eval powpoly 15

def powpoly' : Nat → Polynomial Int Vars MonomialOrder.deglex :=
  λ n => 1⊙[(X,n)] + 1⊙[(Y,n)] + 1⊙[(Z,n)]

#eval List.map powpoly' $ List.ofFn (n:=15) Fin.val

def e_eval : String → Polynomial Int Vars MonomialOrder.deglex
| "e₁" => 1⊙[(X,1)] + 1⊙[(Y,1)] + 1⊙[(Z,1)]
| "e₂" => 1⊙[(X,1), (Y,1)] + 1⊙[(Y,1), (Z,1)] + 1⊙[(X,1), (Z,1)]
| "e₃" => 1⊙[(X,1), (Y,1), (Z,1)]
| _ => 0

instance (o : MonomialOrder Vars) : HPow (Polynomial Int Vars o) Nat (Polynomial Int Vars o) where
  hPow := Nat.sqPow

#eval List.map (λ n => (powpoly n).elim Polynomial.scalar e_eval) $ List.ofFn (n:=12) Fin.val

example : (powpoly 3).elim Polynomial.scalar e_eval = powpoly' 3 := by
  dsimp only [powpoly]
  dsimp only [powpoly']
  dsimp only [Polynomial.elim]
  rfl

example : (powpoly 4).elim Polynomial.scalar e_eval = powpoly' 4 := by
  dsimp only [powpoly]
  dsimp only [powpoly']
  dsimp only [Polynomial.elim]
  rfl

example : (powpoly 5).elim Polynomial.scalar e_eval = powpoly' 5 := by
  dsimp only [powpoly]
  dsimp only [powpoly']
  dsimp only [Polynomial.elim]
  rfl
