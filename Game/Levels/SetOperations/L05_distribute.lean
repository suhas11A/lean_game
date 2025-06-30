import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

World "SetOperations"
Level 5
Title "Basic example in intervals"

Introduction "
Let us understand the concept of union (`∪`) and prove a very famous result in Set theory along the way.

Click on `∪` to read more about it.
"
open Set
/-- Let X, Y and Z be sets. Prove that X∩(Y∪Z) = (X∩Y)∪(X∩Z). -/
Statement (U : Type)(X Y Z : Set U): X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  Hint "Once again we have to prove 2 sets are equal, and our go-to move is ..."
  apply Subset.antisymm
  intro x hx
  Hint "Now in the goal you see a bunch of intersections and unions with a specific precedence, use `rw` to carefully
   to open the definitions of intersection and union."
  rw[mem_union, mem_inter_iff, mem_inter_iff]
  Hint "Similarly simplify intersections and unions at `hx`."
  rw[mem_inter_iff, mem_union] at hx
  Hint "Now use theorems and tactics learned in previous worlds to close the current goal, note that this is now an exercise
   in propositional logic and not of sets."
  rw[and_or_left] at hx
  exact hx
  Hint "We are once again faced with proving a set is subset of another set."
  intro a a_1
  Hint "Similar to previous goal, use `rw` and necessary theorems to simplify intersections and unions in both the goal and the hypotheses."
  rw[mem_inter_iff, mem_union]
  rw[mem_union, mem_inter_iff, mem_inter_iff] at a_1
  Hint "This is also an exercise ni propositional logic similar to previous goal, you can take it from here (Believe in yourself)"
  rw[and_or_left]
  exact a_1

Conclusion "Bored with proving boring results on intersection of Sets?? Well we have a new concept for you."

/-- If `A` and `B` are sets, then `A ∪ B` is the union of `A` and `B`.
To enter the symbol `∪`, type `\union`. -/
DefinitionDoc union as "∪"

NewTheorem and_or_left
NewDefinition union
