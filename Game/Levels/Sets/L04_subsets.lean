import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 4
Title "Basic example in intervals"

Introduction "
This example is from Proposition 2.1.20 in Infinite Descent.
"
open Set
/-- Suppose A ⊆ B, B ⊆ C. Then A ⊆ C. -/
Statement (U : Type)(A B C : Set U)(ha : A ⊆ B)(hb : B ⊆ C): A ⊆ C := by
  intro x h1
  Hint "`ha: A ⊆ B` is a proof of `x ∈ A → x ∈ B`"
  Hint "`h1 : x ∈ A` and `ha: A ⊆ B` together make the proof of `h2 : x ∈ B`"
  Hint "Execute `have h2 : x ∈ B := ha h1`"
  have h2 : x ∈ B := ha h1
  Hint "We know `hb h2` is the proof of `x ∈ C` so execute `exact hb h2`"
  exact hb h2

Conclusion "`exact` can close goals and can be used with complex argument. For example `exact And.intro ha hb` will close the goal `ha ∧ hb`"
