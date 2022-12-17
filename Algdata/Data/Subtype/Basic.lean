/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Subtype

variable {α β : Type _}

def fromProdLeft {p : β → Prop} : α × Subtype p → Subtype (p ∘ Prod.snd (α:=α)) :=
  fun x => Subtype.mk (x.fst, x.snd.val) x.snd.property

def fromProdRight {p : α → Prop} : Subtype p × β → Subtype (p ∘ Prod.fst (β:=β)) :=
  fun x => Subtype.mk (x.fst.val,x.snd) x.fst.property

def toProdLeft {p : β → Prop} : Subtype (p ∘ Prod.snd (α:=α)) → α × Subtype p :=
  fun x => (x.val.fst, ⟨x.val.snd,x.property⟩)

def toProdRight {p : α → Prop} : Subtype (p ∘ Prod.fst (β:=β)) → Subtype p × β :=
  fun x => (⟨x.val.fst,x.property⟩, x.val.snd)

theorem map_val_toProdLeft {p : β → Prop} : Prod.map id Subtype.val ∘ toProdLeft (α:=α) (p:=p) = Subtype.val (p:=p ∘ Prod.snd (α:=α)) := funext (fun _ => rfl)

theorem map_val_toProdRight {p : α → Prop} : Prod.map Subtype.val id ∘ toProdRight (β:=β) (p:=p) = Subtype.val (p:=p ∘ Prod.fst (α:=α)) := funext (fun _ => rfl)

def push {p : β → Prop} (f : α → β) : Subtype (p ∘ f) → Subtype p :=
  fun x => ⟨f x, x.property⟩

@[simp]
theorem val_push {p : β → Prop} {f : α → β} (x : Subtype (p ∘ f)) : (x.push f).val = f x.val := rfl

def translate {p q : α → Prop} : (∀ a, p a → q a) → Subtype p → Subtype q :=
  fun hpq x => ⟨x.val, hpq x.val x.property⟩

@[simp]
theorem val_translate {p q : α → Prop} (hpq : ∀ a, p a → q a) (x : Subtype p) : (x.translate hpq).val = x.val := rfl

def zip {p : α → Prop} {q : β → Prop} : Subtype p → Subtype q → Subtype (α:=α×β) (fun c => p c.1 ∧ q c.2) :=
  fun x y => ⟨⟨x.val,y.val⟩, And.intro x.property y.property⟩

theorem val_zip {p : α → Prop} {q : β → Prop} (x : Subtype p) (y : Subtype q) : (zip x y).val = ⟨x.val,y.val⟩ := rfl

end Subtype