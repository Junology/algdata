/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u v w

variable {Cont : Type u} {idx : Type v} {elem : Type w} {dom : Cont → idx → Prop} [GetElem Cont idx elem dom]

theorem getElem_subst {motive : elem → Prop} : ∀ {x y : Cont} {i j : idx} {hxi : dom x i} {hyj : dom y j}, x = y → i = j → motive x[i] → motive y[j]
| _, _, _, _, _, _, rfl, rfl => id

theorem getElem_eq  {x y : Cont} {i j : idx} (hxy : x = y) (hij : i = j) {hxi : dom x i} (hyj : dom y j := hxy ▸ hij ▸ hxi) : x[i] = y[j] :=
  getElem_subst hxy hij rfl
