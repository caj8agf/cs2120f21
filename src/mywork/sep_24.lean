--1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end

--2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim f,
end

--3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  -- ¬¬p
  -- ¬p → false
  -- (P → false) → false
  assume np,
  have f := np p,
  exact false.elim f,
end

/-
Not not p means that not p implies false
-/
/-
axiom em : ∀ (p : Prop), p ∨ ¬

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evident *why* something is either true or
not true, in that you no longer need a proof of
either P or ¬P to have a proof of P ∨ ¬P.
-/

-- We might need classical (vs constructive) reasoning
#check classical.em
open classical
#check em

--4
theorem neg_elim : ∀ ( P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p np,
  assumption,
  contradiction,
end

--5
theorem demorgan_1 : ∀ (P Q : Prop)