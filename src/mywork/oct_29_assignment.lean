import tactic.ring

def cong_mod_nat (n a b : ℕ) :=
  a%n = b%n

example : cong_mod_nat 4 3 7 :=
begin
  unfold cong_mod_nat,
  exact rfl,
end

example (n : ℕ): equivalence (cong_mod_nat n) :=
begin
  unfold equivalence,
  split,
  --reflexive
    unfold reflexive,
    assume x,
    unfold cong_mod_nat,
  split,
  --symmetric
    unfold symmetric,
    assume x,
    unfold cong_mod_nat,
    assume y,
    assume h,
    rw h,
  --transitive
    unfold transitive,
    assume x y z,
    unfold cong_mod_nat,
    assume xy,
    assume yz,
    rw xy,
    exact yz,
end

/-
English: In order for the relation of congruence, modulus n to 
be equivalent, it must be reflexive, symmetric and transitive.
Therefore, we must prove that for two natural numbers a and b,
the relation that both modulo another natural number n are equal
is reflexive, symmetric and transitive. The equality relation is
all three and therefore, congruence is as well.
-/