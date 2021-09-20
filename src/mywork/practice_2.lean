/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?
/-
Trick question because there is no proof of 
false.
-/

#check or.intro_left

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

/-
We have to give a proof in both directions,
first that P implies P or P, then that P or P
implies P.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume p,
  apply iff.intro _ _,
  apply and.elim_left,
  assume p,
  exact and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume porq,
  apply or.elim porq,
  -- proof of p
  assume p,
  exact or.intro_right Q p,
  -- or proof of q
  assume q,
  exact or.intro_left P q,
  -- backward
  assume qorp,
  apply or.elim qorp,
  assume q,
  apply or.intro_right P q,
  assume p,
  apply or.intro_left Q p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pandq,
  have p : P := and.elim_left pandq,
  have q : Q := and.elim_right pandq,
  exact and.intro q p,
  assume qandp,
  have q : Q := and.elim_left qandp,
  have p : P := and.elim_right qandp,
  exact and.intro p q,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : Q ∨ R := and.elim_right pqr,
  apply or.elim qr,
  -- proof of q
  assume q,
  have pq : P ∧ Q := and.intro p q,
  apply or.intro_left _ _,
  exact pq,
  -- proof of r
  assume r,
  have pr : P ∧ R := and.intro p r,
  apply or.intro_right _ _,
  exact pr,
  -- backward
  assume pqpr,
  apply or.elim pqpr,
  -- proof of P ∧ Q
  assume pq,
  have p : P := and.elim_left pq,
  have q : Q := and.elim_right pq,
  

end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume ppq,
  apply or.elim ppq,
  -- proof of P
  assume p,
  exact p,
  -- proof of P ∧ Q
  assume pq,
  exact and.elim_left pq,
  -- backward
  assume p,
  apply or.intro_left _ _,
  exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  assume pandt,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,

end


