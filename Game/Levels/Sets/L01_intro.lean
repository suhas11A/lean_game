import Game.Metadata
import Mathlib.Data.Set.Basic

World "Sets"
Level 1
Title "Introduction to Subsets"

Introduction "
This example is inspired from Example 2.1.16 from infinite descent, let's prove a basic set theorem using Lean.

To prove A ⊆ B, we need to show that if something is an element of A, then it is also an element of B i.e we
need to prove `x ∈ A → x ∈ B`
(To enter the symbol ⊆ type `\\sub`, and for ∈ type `\\mem` (is a member of) or `\\in`).

To prove this goal the first tactic you're going to use is `intro`. Type in `intro x hx` to get started, this will introduce a new
hypotheses named `hx` with new variable `x` that is needed to prove the goal. Read the documentation on the right by clicking on `intro`.
Alternatively you could execute `intro x` to first introduce a new variable `x` into goal and then introduce a new hypotheses.
"

/-- Suppose A is a set. Then A⊆A. -/
Statement (A : Set ℕ): A ⊆ A := by
  intro x hx
  Hint "Now that we have a goal that matches one of the hypotheses. We use `exact` tactic to close the goal. Read the documentation on the right by clicking on `exact`."
  exact hx

Conclusion "
Congratulations! You have completed your first proof in Sets using LEAN!
"

/-- `exact e` closes the main goal if its target type matches that of `e` i.e `exact hx` closes the goal that matches hypotheses `hx`.  -/
TacticDoc exact

/-- `x ∈ A` means that `x` is an element of `A`.  To enter the symbol `∈`, type
`\mem` or `\in`. -/
DefinitionDoc elt as "∈"

/-- `A ⊆ B` means that `A` is a subset of `B`.  To enter the symbol `⊆`,
type `\sub`. -/
DefinitionDoc sub as "⊆"

NewTactic exact
NewDefinition elt Set sub
