-- 1
example : 0 ≠ 1 :=
begin
  assume h,
  have c := eq.refl 0,
  contradiction,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f := h (eq.refl 0),
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
        have pandq := and.intro p q,
        contradiction,
        --Q not true
        exact or.intro_right _ nq,
      --P not true
      exact or.intro_left _ np,
    --backward
    assume npnq,
    assume pandq,
    have p := and.elim_left pandq,
    have q := and.elim_right pandq,
    apply or.elim npnq,
      --left disjunct
      assume np,
      contradiction,
      --right disjunct
      assume nq,
      contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume nporq,
  cases classical.em P with p np,
    --P true
    have porq := or.intro_left Q p,
    contradiction,
    --P not true
    cases classical.em Q with q nq,
      --Q true
      have porq := or.intro_right P q,
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
      --left disjunct
      assume p,
      exact or.intro_left Q p,
      --right disjunct
      assume npandq,
      have q := and.elim_right npandq,
      exact or.intro_right P q,
    --backward
      assume porq,
      apply or.elim porq,
        --left disjunct
        assume p,
        exact or.intro_left _ p,
        --right disjunct
        assume q,
        cases classical.em P with p np,
          --P true
          exact or.intro_left _ p,
          --P not true
          have npandq := and.intro np q,
          exact or.intro_right P npandq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
    --forward
    assume h,
    have pq := and.elim_left h,
    have pr := and.elim_right h,
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
        --right disjunt
        assume r,
        have qr := and.intro q r,
        exact or.intro_right P qr,
    --backward
    assume h,
    apply or.elim h,
      --left disjunt
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
    assume h,
    have pq := and.elim_left h,
    have rs := and.elim_right h,
    apply or.elim pq,
      --left disjunt
      assume p,
      apply or.elim rs,
        --left disjunt
        assume r,
        have pr := and.intro p r,
        exact or.intro_left _ pr,
        --right disjunt
        assume s,
        have ps := and.intro p s,
        apply or.intro_right _ _,
        exact or.intro_left _ ps,
      --right disjunct
      assume q,
      apply or.elim rs,
        --left disjunct
        assume r,
        have qr := and.intro q r,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        exact or.intro_left _ qr,
        --right disjunct
        assume s,
        have qs := and.intro q s,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        exact or.intro_right _ qs,
    --backward
    assume h,
    apply or.elim h,
      --left true
      assume pr,
      have p := and.elim_left pr,
      have r := and.elim_right pr,
      have pq := or.intro_left Q p,
      have rs := or.intro_left S r,
      exact and.intro pq rs,
      --right true
      assume h1,
      apply or.elim h1,
        --left true
        assume ps,
        have p := ps.left,
        have s := ps.right,
        have pq := or.intro_left Q p,
        have rs := or.intro_right R s,
        exact and.intro pq rs,
        --right true
        assume h3,
        apply or.elim h3,
          --left true
          assume qr,
          have q := qr.left,
          have r := qr.right,
          have pq := or.intro_right P q,
          have rs := or.intro_left S r,
          exact and.intro pq rs,
          --right true
          assume qs,
          have q := qs.left,
          have s := qs.right,
          have pq := or.intro_right P q,
          have rs := or.intro_right R s,
          exact and.intro pq rs,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : _ :=
begin
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
      apply or.elim npq,
        --left disjunct
        assume np,
        assume p,
        contradiction,
        --right disjunct
        assume q,
        assume p,
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