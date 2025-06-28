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
  Hint "Applying `simp` might do a lot of simplification that might not correspond to what you would do if you had to prove on paper, hence use `simp only`."
  Hint "To simplify the unions and intersections only, execute `simp only[mem_inter_iff, mem_union]`."
  rw[mem_union, mem_inter_iff, mem_inter_iff]
  Hint "Similarly simplify intersections and unions at `hx`."
  rw[mem_inter_iff, mem_union] at hx
  Hint "Now use theorems and tactics learned in World-1 to close the current goal."
  and_elim hx into h_1, h_2
  cases h_2
  left
  and_intro
  exact h_1
  exact h
  right
  and_intro
  exact h_1
  exact h
  intro a a_1
  Hint "Similar to previous goal, use `simp only` to simplify both the goal and the hypotheses."
  rw[mem_inter_iff, mem_union]
  rw[mem_union, mem_inter_iff, mem_inter_iff] at a_1
  rw[and_or_left]
  exact a_1

Conclusion "--conc--"

/-- If `A` and `B` are sets, then `A ∪ B` is the union of `A` and `B`.
To enter the symbol `∪`, type `\union`. -/
DefinitionDoc union as "∪"

NewTheorem Set.mem_union lt_trans and_or_left
NewTactic cases left right
NewDefinition union
