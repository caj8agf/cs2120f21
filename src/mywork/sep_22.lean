theorem no_contradition : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume P,
  assume pandnp,
  have p := pandnp.left,
  have np := pandnp.right,
  have f := np p,
  exact false.elim f,
end
