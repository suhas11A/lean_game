import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

World "SetOperations"
Level 4
Title "Basic example in intervals"

Introduction "
Let us prove a very famous and important result in Set theory.
"
open Set
/-- Let X, Y and Z be sets. Prove that X∩(Y∪Z) = (X∩Y)∪(X∩Z). -/
Statement (U : Type)(X Y Z : Set U): X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  Hint "Once again we have to prove 2 sets are equal, and our go-to move is ..."
  apply Subset.antisymm
  intro x hx
  Hint "Now in the goal you see a bunch of intersections and unions, we could use `rw`` to manually rewrite them or use LEAN's `simp` tactic."
  Hint "Applying `simp` might do a lot of simplification that you think is unnecessary hence use `simp only`."
  Hint "to simplify the unions and intersections only, execute `simp only[mem_inter_iff, mem_union]`"
  simp only[mem_inter_iff, mem_union]
  have h_1 := hx.1
  have h_2 := hx.2
  cases h_2
  left
  exact And.intro h_1 h
  right
  exact And.intro h_1 h
  intro a a_1
  rw[mem_inter_iff]
  rw[mem_union]
  rw[mem_union] at a_1
  rw[mem_inter_iff] at a_1
  rw[mem_inter_iff] at a_1
  cases a_1
  rw[and_or_left]
  left
  exact h
  rw[and_or_left]
  right
  exact h

Conclusion "--conc--"


NewTheorem Set.mem_union lt_trans and_or_left
NewTactic cases left right
