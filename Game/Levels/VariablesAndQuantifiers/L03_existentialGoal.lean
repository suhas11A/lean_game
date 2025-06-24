import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 3
Title "Existential Quantifier in the Goal"


Introduction "
Let p(x) be a logical formula with free variable x with range X.
The introduction rule of the existential quantifier (∃) is

(∃I) If a ∈ X and p(a) is true, then ∃x ∈ X, p(x).

This means that to **prove a goal** of the form `∃x ∈ X, p(x)`, it suffices to prove
there is some a ∈ X such that p(a) is true.

If we have a goal of the form `∃x ∈ X, p(x)`, we use `exists_intro y` where y is an element of X
to change the goal into proving p(y) is true."

Statement : ∃n : ℕ, n>0 := by
  exists_intro 1
  Hint "Use the `trivial` tactic to finish the proof."
  trivial

NewTactic exists_intro

Conclusion ""
