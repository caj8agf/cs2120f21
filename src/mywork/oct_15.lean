def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n


--display notation (type := {num, num, num})
def one_to_four : set ℕ := {1, 2, 3, 4}

--comprehension notation (type := {set of nat numbers | predicate})
def empte : set ℕ := { n : ℕ | false }

def complete : set ℕ := { n : ℕ | true }

def evens : set ℕ := {n : ℕ | ev n }

def odds : set ℕ := { n : ℕ | od n }

def evens_union_odds : set ℕ := { n : ℕ | ev n ∨ od n }

def evens_intersects_odds : set ℕ := { n : ℕ | ev n ∧ od n }

def evens_complement : set ℕ := { n : ℕ | ¬ ev n }

def odds_complement : set ℕ := { n : ℕ | ¬ od n }

def evens_intersect_empty : set ℕ := { n : ℕ | ev n ∧ n ∈ empte }

--n ∈ empte ------ n in the empty set; could also just say false

def evens_intersect_complete : set ℕ := {n : ℕ | ev n ∧ true }

def evens_union_empty : set ℕ := { n : ℕ | ev n ∨ false }

def evens_union_complete : set ℕ := { n : ℕ | ev n ∨ true }

--empty set: ∅ 
#check (∅ : set ℕ )

--set membership : ∈ 
#check evens 0
#check 0 ∈ evens
#check 1 ∈ evens

def funnn : set ℕ := { n : ℕ | n > 0 ∧ n < 5 }

--set difference
#check evens \ odds     --evens
#check evens \ evens    --empte
#check evens \ empte    --evens
#check evens \ complete --empte

--complement

def compl_nat (s : set ℕ ) : set ℕ := {a | a ∉ s}
#check compl_nat 

--union: ∪ (in set 1 ∨ set 2)
#check odds ∪ complete    --complete
#check odds ∪ empte       --odds
#check odds ∪ evens       --complete

--intersection: ∩ (in set 1 ∧ set 2)
#check odds ∩ empte       --empte
#check evens ∩ complete   --evens
#check odds ∩ evens       --empte

/-
Product
(s1 : set T)
(s2 : set V)
set of all pairs (t, v)
t ∈ s1 and v ∈ s2
-/

def prodset {T V : Type} (s1 : set T) (s2 : set V) := 
  {pr : T × V | pr.1 ∈ s1 ∧ pr.2 ∈ s2}

#check prodset evens empte    --empte
#check prodset evens odds

--subset: ⊆ 
--s1 ⊆ s2 if every element s1 in s2/some s2 value not in s1
#check evens ⊆ evens      --false

--powerset: 𝒫 s (set of all subsets of s)