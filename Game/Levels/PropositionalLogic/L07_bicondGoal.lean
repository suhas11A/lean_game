import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 7
Title "Biconditional in the Goal"

Introduction "Definition 1.1.28 explains that a biconditional p ↔ q (read as \"p if and only if q\")
is logically equivalent to (p → q) ∧ (q → p). Similar to how proving
p ∧ q requires separate proofs of p and q, p ↔ q
requires separate proofs of p → q and q → p. When the goal is of the form
p ↔ q, use the `iff_intro` to separate the proof into two parts, one where
the goal is to prove p → q and one where the goal is to prove q → p."

Statement (h1: x=3 → y=5) (h2: y=5 → x=3) : x=3 ↔ y=5 := by
  iff_intro
  Hint "Use the `exact` tactic to resolve each of the two new goals."
  exact h1
  exact h2

NewTactic iff_intro

Conclusion ""
