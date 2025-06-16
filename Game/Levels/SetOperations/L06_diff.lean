import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 6
Title "Basic example in intervals"

Introduction "
Following along with Thorem 2.2.31, we will show one of the Demorgans rules for Sets.
"

open Set
/-- Let X, Y and A be sets. Prove that A \ (X ∪ Y) = (A \ X) ∩ (A \ Y). -/
Statement (U : Type)(A X Y : Set U): A \ (X ∪ Y) ⊆ (A \ X) ∩ (A \ Y) := by
  Hint "This example can be proved with theorems and tactics that you have already learnt. Try closing the goal on your own."
  intro x hx
  rw[mem_diff] at hx
  and_elim hx into h1, h2
  simp at h2
  rw[not_or] at h2
  and_elim h2 into a_1, a_2
  simp
  exact And.intro (And.intro h1 a_1) (And.intro h1 a_2)



Conclusion "--conc--"


NewTheorem not_or
NewTactic simp
