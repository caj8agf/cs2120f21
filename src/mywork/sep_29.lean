
lemma not_all : ∃ (n : ℕ), n ≠ 0 :=
begin
  apply exists.intro 2,
  assume neq,
  have eq := eq.refl 2,
  contradiction,
end 

example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff,
  exact eq.refl ff,
end 

example : (exists (b : bool), b && tt = ff) → (∃ (b : bool), true) :=
/-
If there exists a bool, b, such that b and true is equal to false,
 than there is a bool such that the statement is true
-/
begin
  assume h,
  cases h with w pf,
  apply exists.intro w,
  exact true.intro,
end

axioms
  (Ball : Type)             --There are balls
  (Green : Ball → Prop)     --a Ball can be Green
  (Red : Ball → Prop)       --a Ball can be REd
  (b1 b2 : Ball)            --b1 and b2 are Balls
  (b1r : Red b1)            --b1 is red
  (b1g : Green b1)          --b1 is green
  (b2r : Red b2)            --b2 is red


example : (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with b rg,
  have br := and.elim_left rg,
  apply exists.intro b,
  exact br,
end

example : (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,
  cases h with b rg,
  apply exists.intro b,
  apply or.elim rg,
    --left disjunct
    assume br,
    exact or.intro_right _ br,
    --right disjunct
    assume bg,
    exact or.intro_left _ bg,
end

example : (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with b rg,
  apply exists.intro b,
  apply or.elim rg,
    --left disjunct
    assume rb,
    exact rb,
    --right disjunct
    assume gb,
end

example : (∃ (b : Ball), Red b) → 
  (∃ (b : Ball), Red b ∨ Green b) :=
begin
  assume h,
  cases h with b r,
  apply exists.intro b,
  exact or.intro_left _ r,
end

axioms
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

example : 
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  assume e,
  cases h with p pf,
  apply exists.intro p,
  exact pf e,
end


/-
Write formal expressions for each of the following
English language sentences.
-/

-- Everyone likes him or herself

example : ∀ (p : Person), Likes p p := 
begin

end

-- Someone doesn't like him or herself

example : ∃ (p : Person), ¬Likes p p := 
begin
end

-- There is someone likes someone else

example : ∃ (p1 p2 : Person), Likes p1 p2 :=
begin
end

-- No one likes anyone who dislikes them

example : ∀ (p1 p2 : Person), ¬Likes p1 p2 → ¬Likes p2 p1 :=
begin
end

-- Everyone likes anyone who is nice

example : ∀ (p1 p2 : Person), Nice p2 → Likes p1 p2 :=
begin
end

-- No one likes anyone who is not nice

example : ∀ (p1 p2 : Person), ¬Nice p2 → ¬Likes p1 p2 :=
begin
end

