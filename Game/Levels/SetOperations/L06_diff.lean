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
Following along with Example 2.1.17.

To prove the goal
"

open Set
/-- Let X, Y and A be sets. Prove that A\(X∪Y)=(A\X)∩(A\Y). -/
Statement (U : Type)(A X Y : Set U): A \ (X ∪ Y) ⊆ (A \ X) ∩ (A \ Y) := by
  intro x hx
  rw[mem_diff] at hx
  have h1 := hx.1
  have h2 := hx.2
  clear hx
  simp at h2
  rw[not_or] at h2
  have a_1 := h2.1
  have a_2 := h2.2
  simp
  exact And.intro (And.intro h1 a_1) (And.intro h1 a_2)



Conclusion "--conc--"


NewTheorem Set.mem_union lt_trans and_or_left not_or
