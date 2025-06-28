import Game.Metadata
import Mathlib.Data.Set.Basic

World "Sets"
Level 1
Title "Introduction to Subsets"

Introduction "
This example is inspired from Example 2.1.16 from infinite descent, let's prove a basic set theorem using Lean.

A set A is a subset of a set B if all elements of A are also elements of B, so `A ⊆ B` is equivalent to saying `∀ x ∈ A → x ∈ B`.

So to prove a goal of form `A ⊆ B`, we need to show that if something is an element of A, then it is also an element of B i.e we
need to prove `∀ x ∈ A → x ∈ B`
(To enter the symbol ⊆ type `\\sub`, and for ∈ type `\\mem` (is a member of) or `\\in`).

To prove this goal the first theorem you're going to use is `subset_def` which expands `A ⊆ B` into `∀ x ∈ A, x ∈ B`.
Type in `rw [subset_def]` to get started, this will change the goal into `∀ x ∈ A, x ∈ A`. Read the documentation on the right by clicking on `Set.subset_def`.
"
open Set
/-- Suppose A is a set. Then A⊆A. -/
Statement (A : Set ℕ): A ⊆ A := by
  rw [subset_def]
  Hint "Recall how to deal with `∀` in goal from Chapter 1.2, we need to show that any general variable x will satisfy `x ∈ A → x ∈ A` "
  forall_intro x
  Hint "We now have a goal of from `p → q` and you know what to do to prove an implication goal."
  imp_intro hx
  Hint "Now that we have a goal that matches one of the hypotheses. We use `exact` tactic to close the goal."
  exact hx

Conclusion "
Congratulations! You have completed your first proof in Sets using LEAN!
"

/-- `x ∈ A` means that `x` is an element of `A`.  To enter the symbol `∈`, type
`\mem` or `\in`. -/
DefinitionDoc elt as "∈"

/-- `A ⊆ B` means that `A` is a subset of `B`.  To enter the symbol `⊆`,
type `\sub`. -/
DefinitionDoc sub as "⊆"

NewDefinition elt Set sub Set.subset_def
