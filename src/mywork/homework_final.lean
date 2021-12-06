import algebra.algebra.basic tactic.ring

-- #1 Solve problem #1, first sentence only.
-- ∃ (n : ℕ), ∀ (l : ℕ), P l → l < n → P n 

-- #2 Solve at least one of #2 and #3. Give detailed but informal proofs
/-
#2 Show that for every n, 0^2+1^2+2^2+...+n^2 = 1/6*n(1+n)(1+2n)
-/

/-
Informal: 
To prove the above, we use a proof by induction, first proving
the conjecture true for the base case, n = 0, then by proving
that if the conjecture is true for n, than it is true for n+1.

For n=0, we must prove that 0^2 = 1/6*0*(1+0)(1+0). Both sides
simplify to 0 and therefore, the conjecture holds for the base
case.

For the inductive case, we assume that 0^2+1^2+2^2+...+n^2
= 1/6*n(1+n)(1+2n) is true in order to prove that 
0^2+1^2+2^2+...+n^2+(n+1)^2 = 1/6*(n+1)(1+n+1)(1+2(n+1)) is true.
Using our proof that 0^2+1^2+2^2+...+n^2 = 1/6*n(1+n)(1+2n) is true,
we simplify the left side to 1/6*n(1+n)(1+2n) + (n+1)^2. Simplifying
both sides shows that they are equal, thus proving the inductive
case. Therefore, by proof of induction, the above conjecture is true.
-/

-- #1 Give a formal proof for #2 or #3.
--Formal:

def sum_sq : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := (sum_sq n') + (n'.succ * n'.succ)

example : sum_sq 3 = 14 := rfl

def P2 : ℕ → Prop :=
  λ n, 6 * sum_sq n = n * (1+n) * (1 + 2*n)

def conjecture2 := ∀ n, P2 n

theorem sum_sq_opt : conjecture2 :=
begin
  unfold conjecture2,
  assume n,
  unfold P2,
  induction n with n' ih_n',
  -- base case
    apply rfl,
  -- inductive case
    simp [sum_sq],
    rw mul_add,
    rw ih_n',
    rw nat.succ_eq_add_one,
    ring,
end

/-
#3 Show that for every n, 0^3+1^3+…+n^3=1/4*n^2(n+1)^2.
-/

/-
Informal: 
To prove the above, we use a proof by induction, first proving
the conjecture true for the base case, n = 0, then by proving
that if the conjecture is true for n, than it is true for n+1.

For n=0, we must prove that 0^3 = 1/4*0^2*(0+1)^2. Both sides
simplify to 0 and therefore, the conjecture holds for the base
case.

For the inductive case, we assume that 0^3+1^3+...+n^3
= 1/4*n^2(n+1)^2 is true in order to prove that 
0^3+1^3+...+n^3+(n+1)^3 = 1/4*(n+1)^2*(n+2)^2 is true.
Using our proof that 0^3+1^3+...+n^3 = 1/4*n^2*(n+1)^2 is true,
we simplify the left side to 1/4*n^2*(n+1)^2 + (n+1)^3. Simplifying
both sides by simple algebra shows that they are equal, thus proving
the inductive case. Therefore, by proof of induction, the above 
conjecture is true.
-/

--Formal: 

def sum_cub : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := (sum_cub n') + (nat.succ n' * nat.succ n' * nat.succ n')

example : sum_cub 3 = 36 := rfl

def P3 : ℕ → Prop :=
  λ n, 4 * sum_cub n = n * n * (n+1) * (n+1)

def conjecture3 := ∀ n, P3 n

theorem sum_cub_opt : conjecture3 :=
begin
  unfold conjecture3,
  assume n,
  unfold P3,
  induction n with n' ih_n',
  --base case
    apply rfl,
  --inductive case
    simp [sum_cub],
    rw mul_add,
    rw ih_n',
    rw nat.succ_eq_add_one,
    ring,
end

-- #2 Formal or detailed informal proofs 10-13



/-
To test out of the final exam ...

#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9
-/