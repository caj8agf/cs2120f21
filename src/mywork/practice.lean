-- commutativity of ∧ and ∨
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume pandq,
  have p := and.elim_left pandq,
  have q := and.elim_right pandq,
  exact and.intro q p,
  --backward
  assume qandp,
  have q := and.elim_left qandp,
  have p := and.elim_right qandp,
  exact and.intro p q,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume porq,
  apply or.elim porq,
  --left disjunct true
  assume p,
  exact or.intro_right Q p,
  --right disjunct true
  assume q,
  exact or.intro_left P q,
  --backward
  assume qorp,
  apply or.elim qorp,
  --left disjunct true
  assume q,
  exact or.intro_right P q,
  --right disjunct true
  assume p,
  exact or.intro_left Q p,
end

-- associativity of ∧ and ∨
example : ∀ (P Q R : Prop), (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqr,
  have pq := and.elim_left pqr,
  have p := and.elim_left pq,
  have q := and.elim_right pq,
  have r := and.elim_right pqr,
  have qr := and.intro q r,
  exact and.intro p qr,
  --backward
  assume pqr,
  have qr := and.elim_right pqr,
  have p := and.elim_left pqr,
  have q := and.elim_left qr,
  have r := and.elim_right qr,
  have pq := and.intro p q,
  exact and.intro pq r,
end

example : ∀ (P Q R : Prop), (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqr,
  apply or.elim pqr,
  --left disjunct
  assume pq,
  apply or.elim pq,
  --left disjunct
  assume p,
  exact or.intro_left _ p,
  --right disjunct
  assume q,
  have qr := or.intro_left R q,
  exact or.intro_right _ qr,
  --right disjunct
  assume r,
  have qr := or.intro_right Q r,
  exact or.intro_right _ qr,
  --backward
  assume pqr,
  apply or.elim pqr,
  --left disjunct
  assume p,
  have pq := or.intro_left Q p,
  exact or.intro_left _ pq,
  --right dijunct
  assume qr,
  apply or.elim qr,
  --left disjunct
  assume q,
  have pq := or.intro_right P q,
  exact or.intro_left _ pq,
  --right disjunct
  assume r,
  exact or.intro_right _ r,
end

--distributivity
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqr,
  have p := and.elim_left pqr,
  have qr := and.elim_right pqr,
  apply or.elim qr,
  --left
  assume q,
  have pq := and.intro p q,
  exact or.intro_left _ pq,
  --right
  assume r,
  have pr := and.intro p r,
  exact or.intro_right _ pr,
  --backward
  assume pqpr,
  apply or.elim pqpr,
  --left
  assume pq,
  have p := and.elim_left pq,
  have q := and.elim_right pq,
  have qr := or.intro_left R q,
  exact and.intro p qr,
  --right
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
  --left
  assume p,
  have pq := or.intro_left Q p,
  have pr := or.intro_left R p,
  exact and.intro pq pr,
  --right
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
  --left
  assume p,
  exact or.intro_left _ p,
  --right
  assume q,
  apply or.elim pr,
  --left
  assume p,
  exact or.intro_left _ p,
  --right
  assume r,
  have qr := and.intro q r,
  exact or.intro_right P qr,
end

--other properties
example : ∀ (P Q R : Prop), (P → (Q → R)) ↔ (P ∧ Q → R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqr,
  assume pandq,
  have p := and.elim_left pandq,
  have q := and.elim_right pandq,
  exact pqr p q,
  --backward
  assume pqr,
  assume p,
  assume q,
  have pandq := and.intro p q,
  exact pqr pandq,
end

example : ∀ (P Q R : Prop), ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume pqr,
  
end

example : ∀ (P Q : Prop), ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume npq,
  cases (classical.em P) with p np,
  --P true
  have porq := or.intro_left Q p,
  have f := npq porq,
  exact false.elim f,
  --P false
  cases (classical.em Q) with q nq,
  --Q true
  have porq := or.intro_right P q,
  have f := npq porq,
  exact false.elim f,
  --Q false
  exact and.intro np nq,
  --backward
  assume npnq,
  assume pq,
  apply or.elim pq,
  --left disjunct
  assume p,
  have np := and.elim_left npnq,
  have f := np p,
  exact false.elim f,
  --right disjunct
  assume q,
  have nq := and.elim_right npnq,
  have f := nq q,
  exact false.elim f,
end

example : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
begin
  assume P Q,
  assume npnq,
  apply or.elim npnq,
  --left disjunct
  assume np,
  assume pandq,
  have p := and.elim_left pandq,
  have f := np p,
  exact false.elim f,
  --right disjunct
  assume nq,
  assume pandq,
  have q := and.elim_right pandq,
  have f := nq q,
  exact false.elim f,
end

example : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume P,
  assume pnp,
  have p := and.elim_left pnp,
  have np := and.elim_right pnp,
  have f := np p,
  exact false.elim f,
end

example : ∀ (P Q : Prop), P ∧ ¬Q → ¬(P → Q) :=
begin
  assume P Q,
  assume pnq,
  have p := and.elim_left pnq,
  have nq := and.elim_right pnq,
  assume pq,
  have q := pq p,
  have f := nq q,
  exact false.elim f,
end

example : ∀ (P Q : Prop), ¬P → (P → Q) :=
begin
  assume P Q,
  assume np,
  assume p,
  have f := np p,
  exact false.elim f,
end

example : ∀ (P Q : Prop), (¬P ∨ Q) → (P → Q) :=
begin
  assume P Q,
  assume npq,
  assume p,
  apply or.elim npq,
  --left disjunct
  assume np,
  have f := np p,
  exact false.elim f,
  --right disjunct
  assume q,
  exact q,
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

example : ∀ (P : Prop), P ∧ false ↔ false :=
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume pf,
  have f := and.elim_right pf,
  exact f,
  --backward
  assume f,
  exact false.elim f,
end

example : ∀ (P Q : Prop), (P → Q) → (¬Q → ¬P) :=
begin
  assume P Q,
  assume pq,
  assume nq,
  cases classical.em P with p np,
  --P true
  have q := pq p,
  have f := nq q,
  exact false.elim f,
  --P false
  exact np,
end

--2

example : ∀ (P R S : Prop), (P → R ∨ S) → (( P → R) ∨ (P → S)) :=
begin
  assume P R S,
  assume prs,
  
end

example : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
begin
  assume P Q,
  assume npq,
  cases classical.em P with p np,
  cases classical.em Q with q nq,
  --P true Q true
  have pq := and.intro p q,
  have f := npq pq,
  exact false.elim f,
  --P true Q not true
  exact or.intro_right _ nq,
  --P not true
  exact or.intro_left _ np,
end

example : ∀ (P Q : Prop), ¬(P → Q) → P ∧ ¬Q :=
begin
  assume P Q,
  assume npq,
end

example : ∀ (P Q : Prop), (P → Q) → (¬P ∨ Q) :=
begin
  assume P Q,
  assume pq,
  cases classical.em P with p np,
  --P true
  have q := pq p,
  exact or.intro_right _ q,
  --P not true
  exact or.intro_left _ np,
end

example : ∀ (P Q : Prop), (¬Q → ¬P) → (P → Q) :=
begin
  assume P Q,
  assume npnq,
  assume p,
  cases classical.em Q with q nq,
  --Q true
  exact q,
  --Q not true
  have np := npnq nq,
  have f := np p,
  exact false.elim f,
end

example : ∀ (P : Prop), (P ∨ ¬P) :=
begin
  assume P,
  exact classical.em P,
end

example : ∀ (P Q : Prop), (((P → Q) → P) → P) :=
begin
  assume P Q,
  assume pqp,
  
end