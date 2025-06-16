import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 7
Title "Biconditional in the Goal"

Introduction "Definition 1.1.28 explains that the biconditional operator is logically
equivalent to two implication operators. For example, p ↔ q (read as \"p if and only if q\")
is logically equivalent to (p → q) ∧ (q → p). Similar to how proving
p ∧ q requires separate proofs of p and q, p ↔ q (AKA (p → q) ∧ (q → p))
requires separate proofs of p → q and q → p. Use the `constructor` tactic to
transform a goal p ↔ q into two separate goals p → q and q → p."

Statement (h1: x=3 → y=5) (h2: y=5 → x=3) : x=3 ↔ y=5 := by
  constructor
  Hint "Use the `exact` tactic to resolve each of the two new goals."
  exact h1
  exact h2

NewTactic constructor

Conclusion ""
