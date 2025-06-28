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
Following along with Theorem 2.2.31, we will show one of the De Morgan's law for Sets.
"

open Set
/-- Let X, Y and A be sets. Prove that A \ (X ∪ Y) = (A \ X) ∩ (A \ Y). -/
Statement (U : Type)(A X Y : Set U): A \ (X ∪ Y) ⊆ (A \ X) ∩ (A \ Y) := by
  Hint "This example can be proved with theorems and tactics that you have already learnt. Try closing the goal on your own."
  intro x hx
  rw[mem_diff] at hx
  and_elim hx into h1, h2
  rw[mem_union] at h2
  rw[not_or] at h2
  and_elim h2 into a_1, a_2
  rw[mem_inter_iff, mem_diff, mem_diff]
  and_intro
  exact h1
  exact a_1
  exact h1
  exact a_2

Conclusion "--conc--"

NewTheorem not_or
