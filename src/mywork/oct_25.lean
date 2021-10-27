import data.set

example : (3, 9) ∈ { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show { p : ℕ × ℕ | p.2 = p.1 * p.1 } (3, 9),        -- predicate applied to parameter
  show 9 = 3 * 3,
  exact rfl,
end

example : (3, 10) ∈ compl { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show ¬{ p : ℕ × ℕ | p.2 = p.1 * p.1 } (3, 10),
  show ¬10 = 9,
  assume h,
  cases h,
end

theorem eq_is_refl : reflexive (@eq nat) :=
begin
  unfold reflexive,
  assume x,
  exact rfl,
end