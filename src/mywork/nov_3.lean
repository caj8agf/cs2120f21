axioms (Ball : Type) (red : Ball → Prop)
def empty_bucket :=({} : set Ball)
lemma allBallsinEmptyBucketAreRed :
  ∀ (b : Ball), b ∈ empty_bucket → red b :=
begin
  assume b h,
  cases h,
end