import Game.Metadata
import Mathlib.Data.Set.Basic

World "Sets"
Level 1
Title "Introduction to Subsets"

Introduction "
This example is inspired by Example 2.1.16 of Infinite Descent.

A set `A` is a **subset** of a set `B` if all elements of A are also elements of B, so `A ⊆ B` is equivalent to saying `∀ x ∈ A → x ∈ B`.

To prove a goal of form `A ⊆ B`, we need to show that if something is an element of A, then it is also an element of B i.e we
need to prove `∀ x ∈ A → x ∈ B`
(To enter the symbol ⊆ type `\\sub`, and for ∈ type `\\mem` (is a member of) or `\\in`).

To prove this goal the first theorem you're going to use is `subset_def` which expands `A ⊆ B` into `∀ x ∈ A, x ∈ B`.
Type in `rw [subset_def]` to get started, this will change the goal into `∀ x ∈ A, x ∈ A`. Read the documentation on the right by clicking on `Set.subset_def` under the
\"Definitions\" section.
"
open Set
/-- Suppose A is a set. Then A⊆A. -/
Statement (A : Set ℕ): A ⊆ A := by
  rw [subset_def]
  Hint "Recall the proof strategy needed when `∀` appears in the goal, which was introduced in \"Chapter 2: Variables and Quantifiers\"."
  fix x
  assume hx
  exact hx

Conclusion ""

/-- `x ∈ A` means that `x` is an element of `A`.  To enter the symbol `∈`, type
`\mem` or `\in`. -/
DefinitionDoc elt as "∈"

/-- `A ⊆ B` means that `A` is a subset of `B`.  To enter the symbol `⊆`,
type `\sub`. -/
DefinitionDoc sub as "⊆"

NewDefinition elt Set sub Set.subset_def
