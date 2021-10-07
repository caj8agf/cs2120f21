axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,
  --forward
  assume h,
  have f := classical.em (∃ (p : Person), ¬Likes p p),
  cases f with f nf,
    --f true
    exact f,
    --f not true
    --propose new fact, proof to be constructed later
    have contra : ∀ (p : Person), Likes p p := _,
    --prove using propsed fact
    contradiction,
      --prove assumption
      assume p,
      --same trick again!
      have g := classical.em (Likes p p),
      cases g,
        --g true
        exact g,
        --g not true
        have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
        contradiction,
  --backward
  assume h,
  cases h with p pf,
  assume h1,
  have d := h1 p,
  contradiction,
end