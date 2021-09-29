/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pp,
    apply or.elim pp,
      --left disjunct
      assume p,
      exact p,
      --right disjunct
      assume p,
      exact p,
    --backward
      assume p,
      exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pnp,
    exact and.elim_left pnp,
    --backward
    assume p,
    exact and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    --forward
    assume pq,
    apply or.elim pq,
      --left disjunct
      assume p,
      exact or.intro_right Q p,
      --right disjunct
      assume q,
      exact or.intro_left P q,
    --backward
      assume qp,
      apply or.elim qp,
        --left disjunct
        assume q,
        exact or.intro_right P q,
        --right disjunct
        assume p,
        exact or.intro_left Q p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    --forward
    assume pq,
    have p := and.elim_left pq,
    have q := and.elim_right pq,
    exact and.intro q p,
    --backward
    assume qp,
    have q := and.elim_left qp,
    have p := and.elim_right qp,
    exact and.intro p q,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    --forward
    assume pqr,
    have p := and.elim_left pqr,
    have qr := and.elim_right pqr,
    apply or.elim qr,
      --left disjunct
      assume q,
      have pq := and.intro p q,
      exact or.intro_left _ pq,
      --right disjunct
      assume r,
      have pr := and.intro p r,
      exact or.intro_right _ pr,
    --backward
    assume pqpr,
    apply or.elim pqpr,
      --left disjunct
      assume pq,
      have p := and.elim_left pq,
      have q := and.elim_right pq,
      have qr := or.intro_left R q,
      exact and.intro p qr,
      --right disjunct
      assume pr,
      have p := and.elim_left pr,
      have r := and.elim_right pr,
      have qr := or.intro_right Q r,
      exact and.intro p qr,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    --forward
    assume pqr,
    apply or.elim pqr,
      --left disjunct
      assume p,
      have pq := or.intro_left Q p,
      have pr := or.intro_left R p,
      exact and.intro pq pr,
      --right disjunct
      assume qr,
      have q := and.elim_left qr,
      have r := and.elim_right qr,
      have pq := or.intro_right P q,
      have pr := or.intro_right P r,
      exact and.intro pq pr,
    --backward
    assume pqpr,
    have pq := and.elim_left pqpr,
    have pr := and.elim_right pqpr,
    apply or.elim pq,
      --left disjunct
      assume p,
      exact or.intro_left _ p,
      --right disjunct
      assume q,
      apply or.elim pr,
        --left disjunct
        assume p,
        exact or.intro_left _ p,
        --right disjunct
        assume r,
        have qr := and.intro q r,
        exact or.intro_right P qr,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    --forward
    assume ppq,
    exact and.elim_left ppq,
    --backward
    assume p,
    have pq := or.intro_left Q p,
    exact and.intro p pq,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    --forward
    assume ppq,
    apply or.elim ppq,
      --left disjunct
      assume p,
      exact p,
      --right disjunct
      assume pq,
      exact and.elim_left pq,
    --backward
    assume p,
    exact or.intro_left _ p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pt,
    exact true.intro,
    --backward
    assume t,
    exact or.intro_right P t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pf,
    apply or.elim pf,
      --left disjunct
      assume p,
      exact p,
      --right disjunct
      assume f,
      exact false.elim f,
    --backward
    assume p,
    exact or.intro_left _ p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pt,
    exact and.elim_left pt,
    --backward
    assume p,
    exact and.intro p true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
    --forward
    assume pf,
    exact and.elim_right pf,
    --backward
    assume f,
    exact false.elim f,
end
