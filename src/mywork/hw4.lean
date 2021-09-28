-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
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
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume h,
  cases (em P) with p np,
  cases (em Q) with q nq,
  --P true, Q true
  have pandq := and.intro p q,
  have f := h pandq,
  exact false.elim f,
  --P true, Q not true
  apply or.intro_right _ _,
  exact nq,
  --P false
  apply or.intro_left _ _,
  exact np,
  --backward
  assume h,
  assume pandq,
  have p : P := and.elim_left pandq,
  have q : Q := and.elim_right pandq,
  apply or.elim h,
  --left disjunct true
  assume np,
  contradiction,
  --right disjunct true
  assume nq,
  contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  cases (em P) with p np,
  --P true
  have porq := or.intro_left Q p,
  have f := h porq,
  exact false.elim f,
  --P false
  cases (em Q) with q nq,
  --Q true
  have porq := or.intro_right P q,
  have f := h porq,
  exact false.elim f,
  --Q false
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
  --left disjunct is true
  assume p,
  apply or.intro_left _ _,
  exact p,
  --right disjunct is true
  assume npq,
  have q : Q := and.elim_right npq,
  apply or.intro_right _ _,
  exact q,
  --backward
  assume porq,
  apply or.elim porq,
  --left disjunct true
  assume p,
  apply or.intro_left _ _,
  exact p,
  --right disjunct true
  assume q,
  cases (em P) with p np,
  --P true
  apply or.intro_left _ _,
  exact p,
  --P false
  have npandq := and.intro np q,
  apply or.intro_right _ _,
  exact npandq,
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
  have porq : P ∨ Q := and.elim_left pqpr,
  have porr : P ∨ R := and.elim_right pqpr,
  apply or.elim porq,
  --left disjunct true
  assume p,
  apply or.intro_left _ _,
  exact p,
  --right disjunct true
  assume q,
  apply or.elim porr,
  --left disjunct true
  assume p,
  apply or.intro_left _ _,
  exact p,
  --right disjunct true
  assume r,
  have qandr : Q ∧ R := and.intro q r,
  apply or.intro_right _ _,
  exact qandr,
  --backward
  assume pqr,
  apply or.elim pqr,
  --left disjunct true
  assume p,
  have porq : P ∨ Q := or.intro_left Q p,
  have porr : P ∨ R := or.intro_left R p,
  apply and.intro porq porr,
  --right disjunct true
  assume qandr,
  have q : Q := and.elim_left qandr,
  have r : R := and.elim_right qandr,
  have porq : P ∨ Q := or.intro_right P q,
  have porr : P ∨ R := or.intro_right P r,
  apply and.intro porq porr,
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
  have porq : P ∨ Q := and.elim_left pqrs,
  have rors : R ∨ S := and.elim_right pqrs,
  apply or.elim porq,
  -- left disjunct true (porq)
  assume p,
  apply or.elim rors,
  -- left disjunct true (rors)
  assume r,
  have pandr : P ∧ R := and.intro p r,
  apply or.intro_left _ _,
  exact pandr,
  --right disjunct true (rors)
  assume s,
  have pands : P ∧ S := and.intro p s,
  apply or.intro_right _ _,
  apply or.intro_left _ _,
  exact pands,
  --right disjunct true (porq)
  assume q,
  apply or.elim rors,
  --left disjunct true (rors)
  assume r,
  have qandr : Q ∧ R := and.intro q r,
  apply or.intro_right _ _,
  apply or.intro_right _ _,
  apply or.intro_left _ _,
  exact qandr,
  --right disjunct true (rors)
  assume s,
  have qands : Q ∧ S := and.intro q s,
  apply or.intro_right _ _,
  apply or.intro_right _ _,
  apply or.intro_right _ _,
  exact qands,
  --backward
  assume long,
  apply or.elim long,
  --left disjunct true (long)
  assume pandr,
  have p : P := and.elim_left pandr,
  have r : R := and.elim_right pandr,
  have porq : P ∨ Q := or.intro_left Q p,
  have rors : R ∨ S := or.intro_left S r,
  apply and.intro porq rors,
  --right disjunct true (long)
  assume long1,
  apply or.elim long1,
  --left disjunct true (long1)
  assume pands,
  have p : P := and.elim_left pands,
  have s : S := and.elim_right pands,
  have porq : P ∨ Q := or.intro_left Q p,
  have rors : R ∨ S := or.intro_right R s,
  apply and.intro porq rors,
  --right disjunct true (long1)
  assume long2,
  apply or.elim long2,
  --left disjunct true (long2)
  assume qandr,
  have q : Q := and.elim_left qandr,
  have r : R := and.elim_right qandr,
  have porq : P ∨ Q := or.intro_right P q,
  have rors : R ∨ S := or.intro_left S r,
  apply and.intro porq rors,
  --right disjunct true (long2)
  assume qands,
  have q : Q := and.elim_left qands,
  have s : S := and.elim_right qands,
  have porq : P ∨ Q := or.intro_right P q,
  have rors : R ∨ S := or.intro_right R s,
  apply and.intro porq rors,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : (∃ (n : ℕ), ¬ n = 0) → true :=
begin
  assume h,
  cases h with n pf,
  exact true.intro,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume pq,
  have pnp : P ∨ ¬P := classical.em P,
  apply or.elim pnp,
  --left disjunct true
  assume p,
  have q : Q := pq p,
  apply or.intro_right _ _,
  exact q,
  --right disjunct true
  assume np,
  apply or.intro_left _ _,
  exact np,
  assume npq,
  apply or.elim npq,
  --left disjunct true
  assume np,
  assume p,
  contradiction,
  --right disjunct true
  assume q,
  assume p,
  exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume nq,
  cases em P with p np,
  have q : Q := pimpq p,
  have f : false := nq q,
  exact false.elim f,
  exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npnq,
  assume q,
  cases em P with p np,
  exact p,
  have nq : ¬Q := npnq np,
  have f : false := nq q,
  exact false.elim f,
end

