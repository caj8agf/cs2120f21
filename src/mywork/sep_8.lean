/-
Introduction rule for and ∧ 

Given a proof of P and a proof of Q
get back a proof of (P ∧ Q).
-/

axioms (P Q : Prop)

#check P            -- #check command gives you type of object
#check (P ∧ Q)      -- have proposition of P and proposition of Q, combine to make bigger proposition P ∧ Q

axioms (p : P) (q : Q)

example : P ∧ Q := and.intro p q

/-
and.intro is introduction rule for and
takes arguments of proof of p and proof of q
returns proof of p ∧ q
-/


/-
Prove that if arbitrary propositions P and Q
are true (which is to say that we have a proof
of each of them), that the proposition P ∧ Q
is also true.

Proof: The conjecture that P ∧ Q is true
is proved by application of the introduction
rule for and.
-/

example : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro _ _,
  apply eq.refl 0,
  apply eq.refl 1,
end

theorem bar : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro (eq.refl 0) (eq.refl 1),
end

#check bracket

#check and.elim_left bar        --elimination rule proving 0=0
#check and.elim_right bar       --elimination rule proving 1=1

theorem and_commutative : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q h,
  apply and.intro _ _,
  apply and.elim_right h,
  apply and.elim_left h,
end 