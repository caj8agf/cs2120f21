/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
     q : Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p2q,
  assume p,
  exact p2q p,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- True is always true, and therefore, has a proof.

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro



-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- If you have a proof of P and a proof of Q,
you have a proof of P ∧ Q

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), P ∧ Q → P := 
begin
  assume P Q,
  assume pq,
  exact and.elim_left pq,
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- If you have an arbitrary value, t, of Type T and a
proof of Q t can be constructed, there is a proof of 
∀ (t : T), Q.


ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                Q t

-- English language answer here

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- We know that ever t has property Q by the proof, pf. 
You apply the proof, pf, to the value, t to derive a
proof of Q t. In other words, you use pf as a function
with t as the argument.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  (Lynn : Person)
  -- (2) Lynn knows logic
  (Lkl : KnowsLogic Lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn := LogicMakesYouBetterAtCS Lynn (Lkl)

-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := ¬ P -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/-
-- Using proof by negation, in order to prove ¬P,
you must assume P and then prove that P → false. 
In other words, you must show that if P were true, 
it would derive a proof of false. Because false 
cannot be true, P must not be true, which proves ¬P.
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume _¬P_ and show that _there is a contradiction_.
From this derivation you can conclude _¬¬P_.
Then you apply the rule of negation _elimination_
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is _classically_ valid, and that accepting the axiom
of the _excluded middle_ suffices to establish negation
_elimination_ (better called double _negation_ _elimination_)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → (Q ↔ P) :=
begin
  assume P Q,
  assume h,
  have pq := iff.elim_left h,
  have qp := iff.elim_right h,
  apply iff.intro _ _,
    --forward
    exact qp,
    --backward
    exact pq,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 

/-
If Person is a type, and Nice, Talented and Likes are predicates of an
object of type Person, given a proof that for all objects, p, of type
Person that are Nice and Talented, all objects, q, of type Person Likes
p, then if JohnLennon is Nice and Talented, all objects, p, of type Person
Likes JohnLennon.
-/

example : ELJL :=
begin
  unfold ELJL,
  assume Person,
  assume Nice,
  assume Talented,
  assume Likes,
  assume elantp,
  assume JL,
  assume ntJL,
  assume p,
  have nJL := and.elim_left ntJL,
  have tJL := and.elim_right ntJL,
  have lantp := elantp JL,
  have latp := lantp nJL,
  have lap := latp tJL,
  exact lap p,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? _4_
-- list the cases (informaly)
    -- heavy red car
    -- heavy blue car
    -- light red car
    -- light blue car

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (P : Prop), (¬¬P → P) ↔ (P ∨ ¬P) 
  
example : negelim_equiv_exmid :=
begin
  unfold negelim_equiv_exmid,
  assume P,
  apply iff.intro _ _,
    --forward
    assume npp,
    cases classical.em P with p np,
      --P true
      exact or.intro_left _ p,
      --P not true
      exact or.intro_right _ np,
    --backward
      assume pnp,
      assume nnp,
      apply or.elim pnp,
        --left disjunct
        assume p,
        exact p,
        --right disjunct
        assume np,
        contradiction,
end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∀ (x y : Person), Loves x y → Loves y x) → 
    ∀ (p : Person), ∃ (ind : Person), Loves p ind → Loves ind p :=
begin 
  assume symm,
  assume p,
  
end
