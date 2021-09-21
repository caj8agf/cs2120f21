/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?
/-
Trick question because there is no proof of 
false.
-/

#check or.intro_left

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

/-
We have to give a proof in both directions,
first that P implies P or P, then that P or P
implies P.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume p,
  apply iff.intro _ _,
  apply and.elim_left,
  assume p,
  exact and.intro p p,
end

/-
We have to give a proof in both directions,
first that P implies P and P, then that P and
P implies P. 
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume porq,
    apply or.elim porq,
    -- left disjunct true (P)
      assume p,
      exact or.intro_right Q p,
    -- right disjunct true (Q)
      assume q,
      exact or.intro_left P q,
  -- backward
    assume qorp,
    apply or.elim qorp,
    -- left disjunct true (Q)
      assume q,
      apply or.intro_right P q,
    -- right disjunct true (P)
      assume p,
      apply or.intro_left Q p,
end

/-
Proof: First we'll assume that P and Q are propositions.
We must give a proof in both directions, first that
P ∨ Q → Q ∨ P, and then that Q ∨ P → P ∨ Q. 

In order to prove the first, we assume that P ∨ Q is true. 
We can use the elimination rule of ∨ and then show first,
that if we have a proof of p, Q ∨ P is true and second,
that if we have a proof of q, Q ∨ P is true. To do this,
we use the introduction rules of ∨. We apply the right 
introduction rule of ∨ to a proof of p and the proposition,
Q to show Q ∨ P. We apply the left introduction rule of ∨
to a proof of q and the proposition, P to show Q ∨ P.
Therefore, we show that P ∨ Q → Q ∨ P. 

In order the prove the reverse, Q ∨ P → P ∨ Q, we once again 
use the elimination rule of ∨ followed by the left and right 
introduction rules of ∨. By applying the right introduction 
rule to a proof of q and proposition P and the left introduction 
rule to a proof of p and proposition Q, we show Q ∨ P → P ∨ Q.
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume pandq,
  have p : P := and.elim_left pandq,
  have q : Q := and.elim_right pandq,
  exact and.intro q p,
  -- backward
  assume qandp,
  have q : Q := and.elim_left qandp,
  have p : P := and.elim_right qandp,
  exact and.intro p q,
end

/-
Proof: First we'll assume that P and Q are propositions.
We must give a proof in both directions, first that
P ∧ Q → Q ∧ P and second that Q ∧ P → P ∧ Q. In order to
prove the first, we first assume P ∧ Q. We can then use
the left and right elimination rules of ∧ to get a proof p,
of P and a proof q, of Q. We can then apply the introduction
rule of ∧ to q and p to show Q ∧ P. To prove the second, we
assume Q ∧ P. We then use the left and right elimination rules
of ∧ to get a proof q, of Q and a proof p, of P. We can apply 
the introduction rule of ∧ to p and q to show P ∧ Q.
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : Q ∨ R := and.elim_right pqr,
  apply or.elim qr,
  -- left disjunct true (Q)
  assume q,
  have pq : P ∧ Q := and.intro p q,
  apply or.intro_left _ _,
  exact pq,
  -- right disjunct true (R)
  assume r,
  have pr : P ∧ R := and.intro p r,
  apply or.intro_right _ _,
  exact pr,
  -- backward
  assume pqpr,
  apply or.elim pqpr,
  -- left disjunct true (P ∧ Q)
  assume pq,
  have p : P := and.elim_left pq,
  have q : Q := and.elim_right pq,
  have qr : Q ∨ R := or.intro_left R q,
  exact and.intro p qr,
  -- right disjunct true (P ∧ R)
  assume pr,
  have p : P := and.elim_left pr,
  have r : R := and.elim_right pr,
  have qr : Q ∨ R := or.intro_right Q r,
  exact and.intro p qr,
end

/-
Proof: First we'll assume that P Q and R are propositions.
We must give a proof in two directions, first that P ∧ 
(Q ∨ R) → (P ∧ Q) ∨ (P ∧ R), second that (P ∧ Q) ∨ (P ∧ R)
→ P ∧ (Q ∨ R). 

In order to prove the first, we use the left elimination rule
of ∧ to get a proof p, of P and the right elimination rule of ∧ 
to get a proof qr, or Q ∨ R. We will create a proof by case 
analysis, applying the elimination rule of ∨ to qr. First, given 
a proof, q, of Q, we can apply the introduction rule of ∧ to p 
and q to get a proof, pq, of P ∧ Q. We apply the left introduction 
rule of ∨ to pq and the proposition P ∧ R to show (P ∧ Q) ∨ (P ∧ R). 
Second, given a proof r, of R, we can apply the introduction rule of 
∧ to p and r to get a proof, pr, of P ∧ R. We apply the right
introduction rule of ∨ to pr and the proposition P ∧ Q to show
(P ∧ Q) ∨ (P ∧ R).

In order to prove the reverse, we create a proof by case analysis,
applying the elimination rule of ∨ to (P ∧ Q) ∨ (P ∧ R). First,
given a proof, pq, of P ∧ Q, we apply the left and right
elimination rules of ∧ to get proofs p and q, respectively. We
apply the left introduction rule of ∨ to a proof, p, and a
proposition, R, to get a proof, qr, of Q ∨ R. We then apply the 
introduction rule of ∧ to p and qr to get P ∧ (Q ∨ R). Second, given
a proof, pr, of P ∧ R, we apply the left and right elimination
rules of ∧ to get proofs p and r, respectively. We apply the right
introduction rule of ∨ to a proof, r, and a proposition, Q to get a
proof, qr, of Q ∨ R. We apply the introduction rule of ∧ to p and
qr to get P ∧ (Q ∨ R).
-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
  assume pqr,
  apply or.elim pqr,
  -- left disjunct true (P)
  assume p,
  have pq : P ∨ Q := or.intro_left Q p,
  have pr : P ∨ R := or.intro_left R p,
  exact and.intro pq pr,
  -- right disjunct true (Q ∧ R)
  assume qr,
  have q : Q := and.elim_left qr,
  have r : R := and.elim_right qr,
  have pq : P ∨ Q := or.intro_right P q,
  have pr : P ∨ R := or.intro_right P r,
  exact and.intro pq pr,
  -- backward
  assume pqpr,
  have pq : P ∨ Q := and.elim_left pqpr,
  have pr : P ∨ R := and.elim_right pqpr,
  apply or.elim pq,
  -- left disjunct true (P)
  assume p,
  apply or.intro_left _ _,
  exact p,
  -- right disjunct true (Q)
  assume q,
  apply or.elim pr,
  -- left disjunct true (P)
  assume p,
  apply or.intro_left _ _,
  exact p,
  -- right disjunct true (R)
  assume r,
  have qr : Q ∧ R := and.intro q r,
  apply or.intro_right _ _,
  exact qr,
end

/-
Proof: First, we'll assume that P Q and R are propositions.
We must give a proof in two directions, first that P ∨ (Q ∧ R)
→ (P ∨ Q) ∧ (P ∨ R), then that (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R).

In order to prove the first, we create a proof by case analysis,
applying the elimination rule of ∨ to P ∨ (Q ∧ R). Given a proof,
p, of P, we apply the left introduction rule of ∨ to p and a 
proposition Q to get a proof, pq, of P ∨ Q, and the right
introduction rule of ∨ to p and a proposition R to get a proof, pr,
of P ∨ R. We then apply the introduction rule of ∧ to pq and pr to
get (P ∨ Q) ∧ (P ∨ R). Given a proof, qr, of Q ∧ R, we use the 
left and right introduction rules of and to get proofs q and r,
respectively. We apply the right introduction rule of ∨ to q and
a proposition, P to get a proof pq, of P ∨ Q and the right
introduction rule of ∨ to r and a proposition, P to get a proof pr,
of P ∨ R. We then apply the introduction rule of and to pq and pr
to get (P ∨ Q) ∧ (P ∨ R). 

In order to prove the second, we use the left and right elimination
rules of ∧ to get proofs pq and pr of P ∧ Q and P ∧ R, respectively.
We then create a proof by case analysis, applying the elimination rule 
of ∨ to pq. Given a proof, p, of P, we apply the left introduction
rule of ∨ to p in order to show P ∨ (Q ∧ R). Given a proof q, of Q, we
apply the elimination rule of ∨ to pr from above to create another
proof by case analysis. Given a proof p, of P, we apply the left
introduction rule of ∨ to p to show P ∨ (Q ∧ R). Given a proof r, of R,
we apply the introduction rule of ∧ to q and r to get a proof qr, of 
Q ∧ R. We then apply the right introduction rule of ∨ to show P ∨ (Q ∧ R).
-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume ppq,
  exact and.elim_left ppq,
  -- backward
  assume p,
  have pq : P ∨ Q := or.intro_left Q p,
  exact and.intro p pq,
end

/-
Proof: First, we assume that P and Q are propositions. We must
give a proof in two directions, first that P ∧ (P ∨ Q) → P, second
that P → P ∧ (P ∨ Q).

In order to prove the first, we apply the left elimination rule of
∧ to P ∧ (P ∨ Q) to get P.

To show the second, we apply the left introduction rule of ∨ to the 
proof p, of P and the proposition, Q to get the proof, pq, of P ∨ Q.
We then apply the introduction rule of ∧ to p and pq to get P ∧ (P ∨ Q).
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume ppq,
  apply or.elim ppq,
  -- left disjunct true
  assume p,
  exact p,
  -- right disjunct true (P ∧ Q)
  assume pq,
  exact and.elim_left pq,
  -- backward
  assume p,
  apply or.intro_left _ _,
  exact p,
end

/-
Proof: First, we assume that P and Q are propositions. We must give
a proof in two directions, first that P ∨ (P ∧ Q) → P, second that P
→ P ∨ (P ∧ Q). 

In order to prove the first, we create a proof by case analysis,
applying the elimination rule of or to P ∨ (P ∧ Q). Given a proof, p,
of P, we prove P. Given a proof pq, of P ∧ Q, we apply the left
elimination rule of ∧ to get a proof p, of P. 

In order to prove the second, we apply the left introduction rule of ∨
to a proof p, of P and proposition P ∧ Q, to get P ∨ (P ∧ Q).
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume pt,
  apply or.elim pt,
  -- left disjunct true (P)
  assume p,
  exact true.intro,
  -- right disjunct true (true)
  assume t,
  exact true.intro,
  -- backward
  assume t,
  exact or.intro_right P t,
end

/-
Proof: First, we assume that P is a proposition. We must give a proof
in two directions, first that P ∨ true → true and second, that true →
P ∨ true.

In order to prove the first, we create a proof by case analysis, applying
the elimination rule of ∨ to P ∨ true. Given a proof, p, of P, we apply
the introduction rule of true to get a proof of true. Given a proof of true,
we have a proof of true. 

In order to prove the second, we apply the right introduction rule of ∨ to 
our proof of true to get P ∨ true.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume pf,
  apply or.elim pf,
  -- left disjunct true (P)
  assume p,
  exact p,
  -- right disjunct true (false)
  assume f,
  exact false.elim f,
  -- backward
  assume p,
  apply or.intro_left _ _,
  exact p,
end

/-
Proof: First, we assume that P is a proposition. We must give a proof
in two directions, first that P ∨ false → P, second that P → P ∨ false. 

In order to prove the first, we create a proof by case analysis, applying
the elimination rule of ∨ to P ∨ false. Given a proof, p, of P, we have a
proof of P. By applying the elimination rule of false to P ∨ false, we are
left with a proof of P.

In order to prove the second, we apply the left introduction rule of or to
a proof p, of P and a proposition of false.
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume pt,
  exact and.elim_left pt,
  -- backward
  assume p,
  exact and.intro p true.intro,
end

/-
Proof: First, we assume that P is a proposition. We must give a proof
in two directions, first that P ∧ true → P, second that P → P ∧ true.

In order to prove the first, we apply the left elimination rule of ∧ to
get a proof of P. 

In order to prove the second, we apply the introduction rule of ∧ to a proof,
p, of P and the introduction rule of true.
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume pf,
  exact and.elim_right pf,
  -- backward
  assume f,
  exact false.elim f,
end

/-
Proof: First, we assume that P is a proposition. We must give a proof in 
two directions, first that P ∧ false → false, second that false → P ∧ false.

In order to prove the first, we apply the right elimination rule of ∧ to 
P ∧ false. 

To prove the second, we apply the elimination rule of false to false.
-/
