/-
In today's class, we'll continue with our
exploration of the proposition false, its
elimination rule, and fundamental concepts
related to these ideas:

- proof of false elimination
- proof by negation
-/

/-
Review: example of the principle of false elimination,
which we prove by CASE ANALYSIS. If you assume or derive 
a contradiction (and having a proof of false is definitely
a contradiction), then you need go no further, as there 
are no cases in which such a situation can possible arise,
so you have proved the proposition true "in all cases,"
i.e., by case analysis.
-/

example : false → false :=
begin
  assume f,
  cases f,    -- case analysis: there are no cases!
end

/-
In fact, it doesn't matter what your conclusion
is: it will always be true in a context in which
you have a proof of false. And this makes sense,
because if you have a proof of false, then false
is true, so whether a given proposition is true 
or false, it's true, because even if it's false,
well, false is true, so it's also true!
-/

theorem false_elim : ∀ (P : Prop), false → P :=
begin
  assume P,
  assume f,
  cases f,
end

/-
This, then, is the general principle for false
elimination: ANYTHING FOLLOWS FROM FALSE. This
principle gives you a powerful way to prove any
proposition is true (conditional on having such
a proof). 

The theorem states that if you're given any
proposition, P, and a proof, f, of false, then
in that context, you can return a proof of P by
using false elimination. The only problem with
this super-power is that in reality, there is no
proof of false, so there's no real danger of any
old proposition being automatically true! The
rule of false elimination tells you that if 
you're in a situation that can't happen, then
no worries, be happy, you're done (just use
false elimination).
-/

/-
The elimination principle for false is called 
false.elim in Lean. If you are given or can
derive a proof, f, of false, then all you have
to do to finish your proof is to say, "this is
situation can't happen, so we need not consider
it any further." Or, formally, (false.elim f). 
-/

-- Suppose P is *any* (an arbitrary) proposition 
axiom P : Prop

example : false → P :=
begin
  assume f,
  exact false.elim f, -- Using Lean's version
                      -- P is implicit argument
end

/-
SOME THEOREMS INVOLVING FALSE AND NEGATION
-/


-- NO CONTRADICTION

theorem no_contradiction : ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume P,
  assume h,
  have p := h.left,
  have np := h.right,
  have f := np p,
  exact f,
end


-- EXCLUDED MIDDLE

/-
The so-called "law" (it's really an axiom) of the
excluded middle says that any proposition is either
true or false. There's no middle ground. But in the
constructive logic of Lean, this isn't true. 

To prove P ∨ ¬P, as you recall, we need to have 
either a proof of P (in this case  use or.intro_left)
or a proof of ¬P, in which case we use or.intro_right
to prove P ∨ ¬P. But what if we don't have a proof
either way?

There are many important questions in computer science
and mathematics where we don't know either way. If you
call one of those propositions, P, and try to prove P
∨ ¬P in Lean, you just get stuck.
-/
theorem excluded_middle' : ∀ (P : Prop), (P ∨ ¬P) :=
begin
  assume P,
  -- we don't have a proof of either P or of ¬P!
  -- no neither or.inl nor or.inr applies
end

/-
Here's a concrete example: Goldbach's Conjecture

Let P be the conjecture, "every even whole number 
greater than 2 is the sum of two prime numbers."
This conjecture, dating (in a slightly different
form) to a letter from Goldback to Euler in 1742
is still neither proved nor disproved! Below you
will find a placeholder for a proof. Just fill it
in (correctly) and you will win $1M and probably 
a Fields Medal (the "Nobel Prize" in mathematics). 
-/

-- just assume that we have evenness and primeness predicates
axioms (ev : ℕ → Prop) (prime : ℕ → Prop)

-- here's the statment of Goldbach's conjecture
def goldbach_conjecture := 
  ∀ (n : ℕ), 
    n > 2 → 
    (∃ h k : ℕ, n = h + k ∧ prime h ∧ prime k)

-- can you prove it true?
theorem goldbach_conjecture_true : goldbach_conjecture := _

-- can you prove it false?
theorem goldbach_conjecture_false : ¬goldbach_conjecture := _

-- or haven't you yet proved it either way?


/-
So is it true that Goldbach's conjecture is either true 
or it's false, with no other possibility? Well, yes, but
only if you admit the axiom of the excluded middle into
our logic. 
-/

example : goldbach_conjecture ∨ ¬goldbach_conjecture := _

/-
Without this axiom, our only options are or.intro_left 
or or.intro_right applied to proofs/arguments that we do
not have. The axioms of the constructive logic of Lean are
not strong enough to prove the "law of the excluded middle."

Rather, if we want to use it, we have to accept it as
an additional axiom. We thus have two different logics:
one without and one with the law of the excluded middle!
-/

axiom excluded_middle : ∀ (P : Prop), (P ∨ ¬P)

example : goldbach_conjecture ∨ ¬goldbach_conjecture := 
  excluded_middle goldbach_conjecture

/-
That is all it took to add this axiom to our logic. In the
official Lean libraries, it's called classical.em.
-/

#check classical.em     -- Understand what this is saying!

example : goldbach_conjecture ∨ ¬goldbach_conjecture := 
  classical.em goldbach_conjecture

/-
HOW TO USE EXCLUDED MIDDLE.

The real power is in how we *use* this new axiom.
You give it a proposition, P, it gives you a proof
of a disjunction (P ∨ ¬P). Well, what do you do with
a proof of a disjunction? Answer: a case analysis. 

Given a proposition, P, the "strategy," then, is to
a case analysis on "em P." Remember "em P" gives you
a proof of P ∨ ¬P, and its on this proof, of this 
disjunction, that you do a case analysis. In one
case P is assumed true; in the other case, ¬P is
assumed true; *and there are no other cases.* 
-/

/-

At this point you should see that a proof in the
constructive logic of Lean is *informative*. It
tells you *why* a given proposition is true. But 
with excluded middle, a proof of P ∨ ¬P is not 
informative, in that it no longer contains a proof 
of either side.
-/

/-
Here is an example where we apply excluded middle 
to the proposition, ItsRaining, to obtain a proof
of ItsRaining ∨ ¬ItsRaining. 
-/

axiom ItsRaining : Prop -- assume ItsRaining is any proposition

#check excluded_middle ItsRaining     -- apply em to ItsRaining

theorem example_em : ItsRaining ∨ ¬ItsRaining := 
  excluded_middle ItsRaining  -- apply excluded_middle directly to ItsRaining
                              -- to return a proof of ItsRaining ∨ ¬ItsRaining
                              -- by universal instantiation of excluded middle

/-
In Lean's official libraries, excluded middle is called
classical.em (the name is em in the classical namespace).
-/

theorem example_em' : ItsRaining ∨ ¬ItsRaining := 
  classical.em ItsRaining 


/-
PROOF BY NEGATION, AGAIN
-/

/-
Next we return to the negation connective, which
in logic is pronounced "not." Given any proposition,
P, ¬P is also a proposition; and what it means is,
exactly, P → false. If P is true, then false is true,
and false cannot possibly be true, so P must not be.

Thus, to prove ¬P you prove P → false. Another way
to read P → false is that, if we assume that P is
true, we can derive a contradiction, proof of false 
that cannot exist, so P must not be true. MEMORIZE
THIS REASONING.

Again, to prove ¬P, *assume P* and show that in that
context you can derive a contradiction in the form
of a proof of false. This is the strategy call proof
by negation. (THERE WAS A TYPO HERE)
-/

/-
How about we prove ¬(0 = 1) in English.

Proof. By negation. Assume 0 = 1 and show
that this leads to a contradiction. That 
is, show 0 = 1 → false.

The rest of the proof is by case analysis on 
the assumed proof of 0 = 1. The only way to
have a proof of equality is by the reflexive
property of =. But the reflexive property
doesn't imply that there's a proof of 0 = 1. 
So there can be no proof of 0 = 1, and the
assumption that 0 = 1 is thus a contradiction.

We finish the proof by case analysis on the
possible proofs of 0 = 1, of which there are
zero. So in all (zero!) cases, the conclusion
(false) follows. Therefore 0 = 1 → false, which
is to say, ¬(0 = 1) is proved and thus true. 
QED.
-/

example : ¬0 = 1 :=
begin
  show 0 = 1 → false,   -- rewrite goal to a definitionally equal goal
  assume h,
  cases h,                -- there are *zero* ways to build a proof of 0 = 1
                          -- case analysis discharges our "proof obligation"
end

