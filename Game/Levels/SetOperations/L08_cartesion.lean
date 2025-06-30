import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 8
Title "Basic example in intervals"

Introduction "
Following along with Example 2.2.36 we'll learn the concept of Cartesian product.

The cartesian product s ×ˢ t is the set of (a, b) such that a ∈ s and b ∈ t.
"

open Set
/--  Let X be a set. Prove that X × ∅ = ∅. -/
Statement (U : Type)(X: Set U): X ×ˢ (∅ : Set U) = ∅ := by
  apply Subset.antisymm
  intro a ha
  Hint "Say {a} is a tuple of 2 members (x,y) then {a}.1 represents x and {a}.2 represents y. Theorem `mem_prod` can be used to rewrite `{a} ∈ A ×ˢ B` into `{a}.1 ∈ A ∧ {a}.2 ∈ B`."
  rw[mem_prod] at ha
  cases ha.2
  intro a ha
  cases ha


Conclusion "You should now be familiar with Sets, Move on to Next world to explore Functions."

/-- The cartesian product s ×ˢ t is the set of (a, b) such that a ∈ s and b ∈ t.
To enter the symbol `×ˢ`, type `\xs`. -/
DefinitionDoc Set.prod as "×ˢ"

NewTheorem Set.mem_prod
NewDefinition Set.prod
