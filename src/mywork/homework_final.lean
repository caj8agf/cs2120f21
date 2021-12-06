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
#10 Give an informal but detailed proof that for every 
natural number n, 1*n=n, using a proof by induction, 
the definition of multiplication and the theorems 
proved in Section 17.4.
-/

/-
To prove that for every natural number n, 1*n=n, we conduct
a proof by induction. To do so, we must first prove the base
case, that the above is true when n=0, and then the inductive
case, that assuming the above is true for n, it is true for
n+1.

The definition of multplication is as follows:
m*0=0
m*succ(n) = m*n+m

To prove the base case, we must show that 1*0=0. The first 
clause of the definition of multiplication proves this to be
true. 

To prove the inductive case, we first assume that 1*n=n. From
the second clause of the definition of multiplication, we get
1*succ(n)=1*(n)+1=succ(n) which is true by simple algebra.
-/

def mul : nat → nat → nat
| (m) (nat.zero) := nat.zero
| (m) (nat.succ n') := m * n' + m

def Pmul : ℕ → Prop :=
  λ n, mul 1 n = n

theorem Pmult : ∀ n, Pmul n :=
begin
  assume n,
  unfold Pmul,
  induction n with n' ih_n',
  --base case
    exact rfl,
  --inductive case
    simp [mul],
end
/-
#11 Show that multiplication distributes over addition.
In other words, prove that for natural numbers m, n, and
k, m(n+k) = mn + mk. You should use the definitions of
addition and multiplication and facts proved in Section
17.4 (but nothing more).
-/

def mda : ℕ → ℕ → ℕ → Prop :=
  λ m n k, m*(n+k) = m*n+m*k

theorem multdadd : ∀ m n k, mda m n k :=
begin 
  assume m n k,
  unfold mda,
  induction m with m' ih_m',
  -- base case
    ring,
  --inductive case
    ring,    
end

/-
#12 Prove the multiplication is associative, in the same
way. You can use any of the facts proved in Section 17.4
and the previous exercise.
-/

def mulassoc : ℕ → ℕ → ℕ → Prop :=
  λ m n k, (m*n)*k = m*(n*k)

theorem mult_assoc : ∀ m n k, mulassoc m n k  :=
begin
  assume m n k,
  unfold mulassoc,
  induction m with m' ih_m',
  --base case
    ring,
  --inductive case
    ring,
end

/-
#13 Prove that multiplication is commutative.
-/

def mulcommut : ℕ → ℕ → Prop :=
  λ m n, m*n = n*m

theorem mult_commut : ∀ m n, mulcommut m n :=
begin
  assume m n,
  unfold mulcommut,
  induction m with m' ih_m',
  --base case
    ring,
  --inductive case
    ring,
end

--Extra credit

-- #5
/-
Given the definition of the Fibonacci numbers in Section
17.3, prove Cassini's identity: for every n, F2n+1 - Fn+2Fn
= (-1)^n. Hint: in the induction step, write F2n+2 as
Fn+2(Fn+1 + Fn).
-/

-- #9
/-
Let V bet a non-empty set of integers such that the following
two properties hold: 
  If x, y ∈ V, then x-y ∈ V.
  If x ∈ V, then every multiple of x is an element of V.
Prove that there is some d ∈ V, such that V is equal to the
set of multiples of d. Hint: use the least element principle.
-/


/-
To test out of the final exam ...

#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9
-/