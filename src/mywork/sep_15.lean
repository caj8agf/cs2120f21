theorem and_associative : ∀ (P Q R : Prop), ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R)) := 
begin
  assume P Q R h,
  have r : R := and.elim_right h,
  have pq : P ∧ Q := and.elim_left h,
  have p : P := and.elim_left pq,
  have q : Q := and.elim_right pq,
  exact and.intro p (and.intro q r),
end


/-
Problem #1: State precisely and prove that 
∨ is commutative, in English then formally.
-/

/-
Problem #2: State precisely and prove that ∨ 
is associative, first in English then formally.
-/


/-
have proof p : P or proof q : Q or proof p and q
if proof p : P, proposition Q: apply or.intro_right Q p
if proof q : Q, proposition P: apply or.intro_left P q
-/

theorem or_associative : ∀ (P Q : Prop), P ∨ Q → Q ∨ P :=
begin
  assume P Q h,

end

theorem or_commutative : ∀ (P Q R : Prop), (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R) :=
begin
  assume P Q R h,

end