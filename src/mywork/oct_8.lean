example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume porp,
    apply or.elim porp,
    --left
      assume p,
      exact p,
    --right
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
    assume pandp,
    exact and.elim_left pandp,
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
    --left
      assume p,
      exact or.intro_right Q p,
    --right
      assume q,
      exact or.intro_left P q,
  --backward
    assume qp,
    apply or.elim qp,
    --left
      assume q,
      exact or.intro_right P q,
    --right
      assume p,
      exact or.intro_left Q p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pq,
    have p := and.left pq,
    have q := and.right pq,
    exact and.intro q p,
  --backward
    assume qp,
    have q := and.left qp,
    have p := and.right qp,
    exact and.intro p q,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume pqr,
    have p := and.left pqr,
    have qr := and.right pqr,
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
      have p := and.left pq,
      have q := and.right pq,
      have qr := or.intro_left R q,
      exact and.intro p qr,
    --right
      assume pr,
      have p := and.left pr,
      have r := and.right pr,
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
      have q := and.left qr,
      have pq := or.intro_right P q,
      have r := and.right qr,
      have pr := or.intro_right P r,
      exact and.intro pq pr,
  --backward
    assume pqpr,
    have pq := and.left pqpr,
    have pr := and.right pqpr,
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

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume ppq,
    exact and.left ppq,
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
    --left
      assume p,
      exact p,
    --right
      assume pq,
      exact and.left pq,
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
    apply or.elim pt,
    --left
      assume p,
      exact true.intro,
    --right
      assume t,
      exact t,
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
    --left
      assume p,
      exact p,
    --right
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
    exact and.left pt,
  --backward
    assume p,
    have t := true.intro,
    exact and.intro p t,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume pf,
    exact and.right pf,
  --backward
    assume f,
    exact false.elim f,
end


-- 1
example : 0 ≠ 1 :=
begin
  assume h,
  have g := eq.refl 0,
  contradiction,  
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have g := eq.refl 0,
  contradiction,
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  assume np,
  contradiction,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume nnp,
  cases classical.em P with p np,
  --P true
    exact p,
  --P not true
    contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume npq,
    cases classical.em P with p np,
    --P true
      cases classical.em Q with q nq,
      --Q true
        have pq := and.intro p q,
        contradiction,
      --Q not true
        exact or.intro_right  _ nq,
    --P not true
      exact or.intro_left _ np,
  --backward
    assume npnq,
    assume pq,
    apply or.elim npnq,
    --left
      assume np,
      have p := and.left pq,
      contradiction,
    --right
      assume nq,
      have q := and.right pq,
      contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → (¬P ∧ ¬Q) :=
begin
  assume P Q,
  assume npq,
  cases classical.em P with p np,
  --P true
    have pq := or.intro_left Q p,
    contradiction,
  --P not true
    cases classical.em Q with q nq,
    --Q true
      have pq := or.intro_right P q,
      contradiction,
    --Q not true
      exact and.intro np nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pnpq,
    apply or.elim pnpq,
    --left
      assume p,
      exact or.intro_left Q p,
    --right
      assume npq,
      have q := and.right npq,
      exact or.intro_right P q,
  --backward
    assume pq,
    apply or.elim pq,
    --left
      assume p,
      exact or.intro_left _ p,
    --right
      assume q,
      cases classical.em P with p np,
      --P true
        exact or.intro_left _ p,
      --P not true
        have npq := and.intro np q,
        exact or.intro_right P npq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume pqpr,
    have pq := and.left pqpr,
    have pr := and.right pqpr,
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
  --backward
    assume pqr,
    apply or.elim pqr,
    --left
      assume p,
      have pq := or.intro_left Q p,
      have pr := or.intro_left R p,
      exact and.intro pq pr,
    --right
      assume qr,
      have q := and.left qr,
      have r := and.right qr,
      have pq := or.intro_right P q,
      have pr := or.intro_right P r,
      exact and.intro pq pr,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  --forward
    assume pqrs,
    have pq := and.left pqrs,
    have rs := and.right pqrs,
    apply or.elim pq,
    --left
      assume p,
      apply or.elim rs,
      --left
        assume r,
        have pr := and.intro p r,
        exact or.intro_left _ pr,
      --right
        assume q,
        have pq := and.intro p q,
        apply or.intro_right _ _,
        exact or.intro_left _ pq,
    --right
      assume q,
      apply or.elim rs,
      --left
        assume r,
        have qr := and.intro q r,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        exact or.intro_left _ qr,
      --right
        assume s,
        have qs := and.intro q s,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        exact or.intro_right _ qs,
  --backward
    assume h1,
    apply or.elim h1,
    --left
      assume pr,
      have p := and.left pr,
      have r := and.right pr,
      have pq := or.intro_left Q p,
      have rs := or.intro_left S r,
      exact and.intro pq rs,
    --right
      assume h2,
      apply or.elim h2,
      --left
        assume ps,
        have p := and.left ps,
        have s := and.right ps,
        have pq := or.intro_left Q p,
        have rs := or.intro_right R s,
        exact and.intro pq rs,
      --right
        assume h3,
        apply or.elim h3,
        --left
          assume qr,
          have q := and.left qr,
          have r := and.right qr,
          have pq := or.intro_right P q,
          have rs := or.intro_left S r,
          exact and.intro pq rs,
        --right
          assume qs,
          have q := and.left qs,
          have s := and.right qs,
          have pq := or.intro_right P q,
          have rs := or.intro_right R s,
          exact and.intro pq rs,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n : ℕ), n ≠ 0 :=
begin
  apply exists.intro 1,
  assume h,
  have g := eq.refl 0,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pq,
    cases classical.em P with p np,
    --P true
      have q := pq p,
      exact or.intro_right _ q,
    --P not true
      exact or.intro_left Q np,
  --backward
    assume npq,
    assume p,
    apply or.elim npq,
    --left
      assume np,
      contradiction,
    --right
      assume q,
      exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pq,
  assume nq,
  cases classical.em P with p np,
  --P true
    have q := pq p,
    contradiction,
  --P not true
    exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npnq,
  assume q,
  cases classical.em P with p np,
  --P true
    exact p,
  --P not true
    have nq := npnq np,
    contradiction,
end



axioms (T : Type) (Q : Prop) (f : ∀ (t : T), Q) (t : T)
example : Q := f t
#check f
