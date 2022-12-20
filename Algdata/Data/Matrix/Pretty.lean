/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Algdata.Init.Fin
import Algdata.Data.Matrix.Basic

namespace Matrix

variable {α : Type _} [ToString α] {r c : Nat}

def padding (wd : Nat) (s : String) : String :=
  let pd := "".pushn ' ' (wd - s.length)
  pd ++ s

def intercalateAppend (punct : String) (lhs rhs : String) : String :=
  if ¬lhs.isEmpty ∧ ¬rhs.isEmpty
  then lhs ++ punct ++ rhs
  else lhs ++ rhs

instance instMonadLiftID (m : Type _ → Type _) : MonadLiftT m m where
  monadLift := id

-- Pretty printer
def pretty (a : Matrix α r c) : String := Id.run do
  let mut ss := a.entry.map toString
  let wd := Array.foldl (fun k x => Nat.max k x.length) 0 ss
  ss := ss.map (padding wd)
  Fin.foldAllM (n:=r) "" $ fun i str => do
    let mut rowss := ""
    for s in ss[i.val*c : i.val*c + c] do
      rowss := intercalateAppend " " rowss s
    pure $ intercalateAppend "\n" str ("│" ++ rowss ++ "│")

end Matrix