example : ∀ (T : Type) (x y z : T), x = y → y = z → z = x :=
begin
  assume T,
  assume x y z,
  assume h1 h2,
  apply eq.symm _,
  apply eq.trans h1 h2,
end