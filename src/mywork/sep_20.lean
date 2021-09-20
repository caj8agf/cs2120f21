/-
given proposition, P, can form new proposition,
¬P, "not P". Define in way to assert P is not
true

"It is true that P is not true" - should be a proof
that shows that P is not true

If ¬P is true, there should be a proof of it.
What the proof should show is that *there can
be no proofs of P*

If P were true, then something that is completely
impossible would happen. Because the impossible can't
happen, there must be no proof of P.

"the impossible thing" is a proof of false.
have defined false to be exactly a proposition with
no proofs (otherwise it'd be true), so to have a 
proof of false is an impossibility.

-/

example : false → false :=
begin
  assume f,
  exact f,
end

example : false → true :=
begin
  assume f,
  exact true.intro,
end 

example : true → false :=
begin
  assume t,
  --stuck
end


/-
define ¬P to be proposition, P → false. 
Means there is a proof of P → false, then you
can conclude ¬P. **intro rule for ¬. 
-/

example : ¬ false :=
begin
  assume f,
  exact f,
end

example : ¬ 0 = 1 :=
begin
  assume h,
  
end
