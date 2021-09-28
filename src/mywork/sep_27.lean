def pythagorean_triple (a b c : ℕ) : Prop :=
  a*a + b*b = c*c

example : ∃ (a b c : ℕ), pythagorean_triple a b c :=
begin
  
end