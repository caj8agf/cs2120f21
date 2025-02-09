/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- returns a β value and for every α value, if
it satisfies the predicate p than the resulting
β value from the function satisfies the predicate
q, than if there is an α value that satisfies
the predicate p than there must be a β value that
satisfies the predicate q.
-/


-- Give your formal proof here
begin
  assume h,
  assume i,
  cases h with f h,
  cases i with a j,
  have k := h a,
  have m := k j,
  apply exists.intro (f a),
  exact m,
end
  

/- 
PART II: BASIC SET THEORY

stay tuned!
-/
