/-
Operations on relations
-/

variables (α β γ : Type)

def inverse (r : α → β → Prop) : β → α → Prop :=
λ (b : β) (a : α), r a b 

