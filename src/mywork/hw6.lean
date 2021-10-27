import data.set

/-
1 - Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  assume α,
  assume L,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    exact h.left,
  --backward
    assume h,
    apply and.intro h h,
end

/-
2 - Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

theorem union_commutative : ∀ (α : Type) (L M : set α), L ∪ M = M ∪ L :=
begin
  assume α, 
  assume L M,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    cases h,
    --left
      apply or.intro_right _ h,
    --right
      apply or.intro_left _ h,
  --backward
    assume h,
    cases h,
    --left
      apply or.intro_right _ h,
    --right
      apply or.intro_left _ h,
end

/-
English: To prove that union is commutative, you have to
prove that there is a value, x, in L ∪ M if and only if 
that value is also in M ∪ L. To do so, you must provide
a proof of both directions.

To prove the forward direction, you must prove that x is
in M ∪ L. There is a proof that x is in L ∪ M which
provides two cases. First, if x is in L, than common sense
presents that x would also be in M ∪ L. Second, if x is in
M, than common sense once again presents that x would also
be in M ∪ L. 

To prove the backward direction, you must prove that x is
in L ∪ M. There is a proof that x is in M ∪ L which 
provides two cases. First, if x is in M, than common sense 
presents that x would also be in L ∪ M. Second, if x is in
L, than common sense once again presents that x would also
be in M ∪ L.
-/

/-
3 - Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

lemma subset_reflexive : ∀ (α : Type) (L : set α), L ⊆ L :=
begin
  assume α,
  assume L,
  assume a,
  assume h,
  exact h,
end

/-
English: To prove that the subset relation is reflexive,
you must prove that if L is a set of type set α, that all
values in L are also in L. This is common sense.
-/

lemma subset_transitive : ∀ (α : Type) (L M N : set α), L ⊆ M → M ⊆ N → L ⊆ N := 
begin 
  assume α,
  assume L M N,
  assume lm,
  assume mn,
  assume a,
  assume l,
  have m := lm l,
  exact mn m,
end

/-
English: To prove that the subset relation is transitive,
you must prove that if L M and N are all sets of type set
α, L is a subset of M and M is a subest of N than L is 
also a subset of N. By commone sense, you know that all
values in L are also in M and because all values in M are
also in N, all values in L must also be in N. 
-/

theorem subset_reflexive_and_transitive : 
  (∀ (α : Type) (L : set α), L ⊆ L) ∧
  (∀ (α : Type) (L M N : set α), L ⊆ M → M ⊆ N → L ⊆ N) :=
begin
  have srefl := subset_reflexive,
  have strans := subset_transitive,
  exact and.intro srefl strans,
end

/-
English: To prove that the subset relation is transitive
and reflexive, you must provide a proof that the relation
is transitive and a proof that the relation is reflexive.
These proofs are given above.
-/

/-
4 - Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

lemma union_associative : ∀ (α : Type) (L M N : set α), (L ∪ M) ∪ N = L ∪ (M ∪ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    apply or.elim h,
    --left
      assume lm,
      apply or.elim lm,
      --left
        assume l,
        exact or.intro_left _ l,
      --right
        assume m,
        exact or.intro_right _ (or.intro_left _ m),
    --right
      assume n,
      exact or.intro_right _ (or.intro_right _ n),
  --backward
    assume h,
    apply or.elim h,
    --left
      assume l,
      exact or.intro_left _ (or.intro_left _ l),
    --right
      assume mn,
      apply or.elim mn,
      --left
        assume m,
        exact or.intro_left _ (or.intro_right _ m),
      --right
        assume n,
        exact or.intro_right _ n,
end

/-
English: To prove that union is associative, one must prove that
(L ∪ M) ∪ N is equal to L ∪ (M ∪ N). To do so, you must show
that there is a value, x, that is in the first if and only
if it is in the second. To do so you must provide a proof
of both directions.

To prove the forward direction you must prove that x is in 
L ∪ (M ∪ N) given a proof of (L ∪ M) ∪ N. The proof provides
two cases. The first, that x is in L ∪ M and the second, that 
x is in N. The first case provides two more cases, first that 
x is in L and second that x is in M. If x is in L, than it is 
common sense that x must be in L ∪ (M ∪ N) as it is an 
intersection between L and M ∪ N. If x is in M than it is 
common sense that it is in M ∪ N and therefore in L ∪ (M ∪ N).
If x is in N, than it is once again common sense that it is in
M ∪ N and therefore in L ∪ (M ∪ N).

To prove the reverse direction you must prove that x is in (L 
∪ M) ∪ N given a proof of L ∪ (M ∪ N). The proof provides two
cases. The first, that x is in L and the second, that x is in
M ∪ N. If x is in L than it is common sense that x is in L ∪ M 
and therefore in (L ∪ M) ∪ N. The second case provides two more
cases, first that x is in M and second that x is in N. If x is
in M, than it is once again common sense that x is in L ∪ M and
therefore in (L ∪ M) ∪ N. If x is in N than it is common sense
that it is in (L ∪ M) ∪ N as.
-/

lemma intersection_associative : ∀ (α : Type) (L M N : set α), (L ∩ M) ∩ N = L ∩ (M ∩ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    have lm := and.left h,
    have n := and.right h,
    have l := and.left lm,
    have m := and.right lm,
    exact and.intro l (and.intro m n),
  --backward
    assume h,
    have l := and.left h,
    have mn := and.right h,
    have m := and.left mn,
    have n := and.right mn,
    exact and.intro (and.intro l m) n,
end

/-
English: To prove that intersection is associative, one must
prove that (L ∩ M) ∩ N is equal to L ∩ (M ∩ N). To do so, you
must show that there is a value, x, that is in the first if and
only if it is in the second. In order to do this, you must
provide a proof in both directions.

To prove the forward direction you must prove that x is in L ∩ 
(M ∩ N) given a proof that x is in (L ∩ M) ∩ N. This proof provides
a proof that x is in L ∩ M and in N. The proof that x is in L ∩ M 
in turn shows that there is a proof that x is in L and in M. From 
these you can derive a proof that x is in M ∩ N and from there a proof
that x is in L ∩ (M ∩ N).

To prove the backward direction you must prove that x is in (L ∩
M) ∩ N given a proof that x is in L ∩ (M ∩ N). This proof provides 
a proof that x is in L and in M ∩ N. The proof that x is in M ∩ N
in turn shows that there is a proof that x is in M and in N. From
these you can derive a proof that x is in L ∩ M and from there a proof
that x is in (L ∩ M) ∩ N.
-/

theorem un_and_in_associative : 
  (∀ (α : Type) (L M N : set α), (L ∪ M) ∪ N = L ∪ (M ∪ N)) ∧ 
  (∀ (α : Type) (L M N : set α), (L ∩ M) ∩ N = L ∩ (M ∩ N)) :=
begin
  have un_as := union_associative,
  have in_as := intersection_associative,
  apply and.intro un_as in_as,
end

/-
English: To prove that ∪ and ∩ are associative, you must provide
a proof that ∪ is associative and  proof that ∩ is associative.
These proofs are given above.
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
5 - Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

theorem intersection_left_distributive_over_intersection : 
  ∀ (α : Type) (L M N : set α), L ∩ (M ∩ N) = (L ∩ M) ∩ (L ∩ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    have l := h.left,
    have mn := h.right,
    have m := mn.left,
    have n := mn.right,
    exact and.intro (and.intro l m) (and.intro l n),
  --backward
    assume h,
    have lm := h.left,
    have l := lm.left,
    have m := lm.right,
    have ln := h.right,
    have n := ln.right,
    exact and.intro l (and.intro m n),
end

/-
English: To prove that ∩ is left-distributive over ∩, you
must prove that L ∩ (M ∩ N) is equal to (L ∩ M) ∩ (L ∩ N).
To do so, you must show that x is in the first if and only
if it is in the second. In order to do this, you must provide
a proof in both directions.

To prove the forward direction, you must provide a proof that
x is in (L ∩ M) ∩ (L ∩ N) given a proof that x is in L ∩ (M ∩ N).
The proof provides proofs that x is in L, M and N. Based on these
proofs, it is common sense that there is a proof that x is in
L ∩ M as well as in L ∩ N and therefore, there is a proof of
(L ∩ M) ∩ (L ∩ N).

To prove the backward direction, you must provide a proof that
x is in L ∩ (M ∩ N) given a proof that x is in (L ∩ M) ∩ (L ∩ N).
The proof provides proofs that x is in L ∩ M as well as L ∩ N.
These proofs in turn provide proofs that x is in L, M and N. 
Based on these proofs, it is common sense that there is a proof
that x is in M ∩ N and therefore, there is a proof of L ∩ (M ∩ N).
-/

/-
6 - Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

theorem union_left_distributive_over_intersection :
  ∀ (α : Type) (L M N : set α), L ∪ (M ∩ N) = (L ∪ M) ∩ (L ∪ N) :=
begin
  assume α,
  assume L M N,
  apply set.ext _,
  assume x,
  apply iff.intro _ _,
  --forward
    assume h,
    apply or.elim h,
    --left
      assume l,
      exact and.intro (or.intro_left _ l) (or.intro_left _ l),
    --right
      assume mn,
      have m := mn.left,
      have n := mn.right,
      exact and.intro (or.intro_right _ m) (or.intro_right _ n),
  --backward
    assume h,
    have lm := h.left,
    have ln := h.right,
    apply or.elim lm,
    --left
      assume l,
      exact or.intro_left _ l,
    --right
      assume m,
      apply or.elim ln,
      --left
        assume l,
        exact or.intro_left _ l,
      --right
        assume n,
        exact or.intro_right _ (and.intro m n),
end

/-
English: To prove that ∪ is left-distributive over ∩, you must 
prove that L ∪ (M ∩ N) is equal to (L ∪ M) ∩ (L ∪ N). To do so
you must show that x is in the first if and only if it is in the 
second. To do this, you must provide a proof in both directions.

To prove the forward direction, you must provide a proof that x is
in (L ∪ M) ∩ (L ∪ N) given a proof that x is in L ∪ (M ∩ N). The
proof gives two cases, the first that x is in L and the second 
that x is in M ∩ N. If x is in L then by common sense x is also in
L ∪ M as well as L ∪ N. Therefore by common sense you have a proof
of (L ∪ M) ∩ (L ∪ N). The second case provides two proofs, first
that x is in M and second that x is in N. Based on these proofs,
you have a proof that x is in L ∪ M as well as in L ∪ N and 
therefore, by common sense you have a proof of (L ∪ M) ∩ (L ∪ N).

To prove the backward direction, you must provide a proof that x
is in L ∪ (M ∩ N) given a proof that x is in (L ∪ M) ∩ (L ∪ N).
The proof provides proofs that x is in both L ∪ M and L ∪ N. The 
first proof provides two cases. The first, that x is in L and the
second that x is in M. If x is in L, than by common sense you have
a proof of L ∪ (M ∩ N). However, if x is in M you must consider the
two cases that the proof of L ∪ N provides. The first being that x
is in L and the second being that x is in N. Once again, if x is in
L than by common sense you have a proof of L ∪ (M ∩ N). In the case
that x is in M as well as N, there is a proof of M ∩ N and therefore,
a proof of L ∪ (M ∩ N).
-/