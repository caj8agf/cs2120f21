def cong_mod (n a b : ℤ) : Prop :=
  ∃ k, a - b = k * n

def cong_mod_n_is_equiv_relation (n : ℤ) : Prop := 
  equivalence (cong_mod n) 

example : cong_mod (4:ℤ) (6:ℤ) (14:ℤ) :=
begin
  unfold cong_mod,
  apply exists.intro (-2:ℤ),
  apply rfl,
end

example (n : ℤ) : cong_mod_n_is_equiv_relation n :=
begin
  unfold cong_mod_n_is_equiv_relation,
  unfold equivalence,
  split,

  --reflexive
  unfold reflexive,
  assume k,
  unfold cong_mod,
  apply exists.intro (0 : ℤ),
  sorry,

  --symmetric
  split,
  unfold symmetric,
  assume x y,
  unfold cong_mod,
  assume h,
  cases h with v pf,
  apply exists.intro (-v),
  have lemma1 : -v * n = -(v * n) := sorry,
  rw lemma1,
  rw <- pf,
  have lemma2 : -(x - y) = y - x := sorry,
  rw lemma2,

  --transitive
  unfold transitive,
  assume x y z,
  unfold cong_mod,
  assume h,
  assume i,
  cases h with v ph,
  cases i with v1 pi,
  apply exists.intro(v+v1),
  rw int.distrib_right _ _ _,
  rw <- pi,
  rw <- ph,
  sorry,
end