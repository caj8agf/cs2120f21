/-
Prove that equality is symmetric.
-/

theorem eq_symm :
  ∀ (T : Type) (x y : T), x = y → y = x :=
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y),
    rw e,
  end


/-
Proof: First we'll assume that T is any type and
objects x and y and this type. What remains to be
shown is that x = y → y = x. To prove this, we'll
assume the premise, that x = y, and in this context
we to prove y = x. But by the axiom of the
substitutability of equals, and using the fact that
x = y, we can rewrite x in the goal as a y, yielding
y = y as our new proof goal. But this is true by the
axiom of reflexivity of equality. QED.
-/

/-
Prove that equality is transitive.
-/

theorem eq_trans :
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
  begin
    assume T,
    assume x y z,
    assume e1,
    assume e2,
    rw e1,
    exact e2,
  end


