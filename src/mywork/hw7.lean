import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume h,
  unfold asymmetric,
  assume asymm,
  cases h with b h,
  unfold reflexive,
  assume refl,
  have rbb := refl b,
  have nrbb := asymm rbb,
  contradiction,
end

/-
English: Given a proof that there exists a value b of type β,
and that the relation r is asymmetric, in order to proof that r
is not reflexive, you must prove that a proof that r is reflexive
implies false. Assuming that the relation r is reflexive gives a 
proof that b is related to itself, b. However, applying the proof
that r is asymmetric to the proof that b is related to b gives a
proof that b is not related to b. This provides a contradiction,
proving that a proof that r is reflexive implies false.
-/

/-
No, the proposition would not be true if the first condition, that 
β is inhabited, were removed because the proposition would not hold
if β were an empty set. Without the proof that β is inhabited, we
cannot assume that it is not an empty set and therefore cannot prove
the proposition to be true.
-/

/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive,
  assume trans,
  unfold reflexive,
  assume refl,
  unfold asymmetric,
  assume asymm,

end

/-
No, this conjecture is not logically valid because if the set defined
by the relation r is empty, than the conjecture would be false due to
the universal generalization over an empty set which states that any
generalization about an empty set is true.
-/

example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume h,
  unfold transitive,
  assume trans,
  unfold reflexive,
  assume refl,
  cases h with b h,
  unfold asymmetric,
  assume asymm,
  have rbb := refl b,
  have nrbb := asymm rbb,
  contradiction,
end



/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1s s2s,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  apply iff.intro _ _,
  --forward
    assume xs1,
    apply s1s2 xs1,
  --backward
    assume xs2,
    apply s2s1 xs2,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end

/-
English: To prove that for all natural numbers n, 1 divides n, you
must provide a proof that there exists a natural number, k, that 
when multiplied by 1 equals n. To do so, you must provide a witness,
n and a proof that n = n * 1 which is true by basic algebra.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/-
English: To prove that for all natural numbers, n, n divides n, you 
must provide a proof that there exists a natural number, k, that
when multiplied by n equals n. To do so, you must provide a witness,
1, and a proof that n = 1 * n which is true by basic algebra.
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive,
  assume x,
  unfold divides,
  apply exists.intro 1,
  ring,
end 

/-
English: To prove that divides is reflexive, you must prove that for
all natural numbers, x, x divides iteslf. To do so, you must provide
a witness, 1, and a proof that x = 1 * x which is true by basic algebra.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive,
  assume x y z,
  unfold divides,
  assume xdy,
  assume ydz,
  cases xdy with n xdy,
  cases ydz with m ydz,
  apply exists.intro (n*m),
  rw ydz,
  rw xdy,
  ring,
end 

/-
English: In order to prove that divides is transitive, you must prove that
for all natural numbers x y z, if x divides y and y divides z than x divides
z. Given the proof that x divides y, there is a witness, n, such
that there is a proof that y = n * x. Additionally, given the proof
that y divides z, there is a witness, m, such that there is a proof that
z = m * y. To prove that x divides z, you must provide a witness n * m, and a
proof that z = n * m * x. Given the proof that z = m * y, we can rewrite the
goal to be m * y = n * m * x and given the proof that y = n * x, we can
rewrite that to be m * n * x = n * m * x which is true by basic algebra.
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
No, divides is not symmetric. For example divides 1 2 is true
because there is a natural number, 2 that if multiplied by 1
is equal to 2. However, divides 2 1 is not true because to get
1 from 2 you must multiply 2 by 1/2 which is not a natural number.
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric,
  assume x y,
  unfold divides,
  assume xdy,
  assume ydx,
  cases xdy with n xdy,
  cases ydx with n ydx,
  -- rw xdy,
  -- rw ydx,
end

/-
English: 
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric,
  assume asymm,
  unfold irreflexive,
  assume x,
  assume rxx,
  have nrx := asymm rxx,
  contradiction,
end

/-
English: To prove that r is irreflexive, we must prove that
the relation r, is not reflexive by proving that a proof 
that r is reflexive would imply a proof of false. To do so,
we assume that r is reflexive. This gives us a proof that
for all values, x, of type β, x is related to x. Given the
proof that r is asymmetric and the proof that x is related to
x, a proof that x is not related to x is generated. This leads
to a contradiction and shows that a proof that r is reflexive
implies a proof of false.
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive,
  assume irrefl,
  unfold transitive,
  assume trans,
  unfold asymmetric,
  assume x y,
  assume rxy,
  assume ryx,
  
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive,
  assume trans,
  unfold symmetric,
  assume nsymm,
  unfold irreflexive,
  assume irrefl,
  
end


end relation
