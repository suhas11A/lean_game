import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 7
Title "Biconditional in the Goal"

Introduction "
A biconditional (↔) is defined by declaring p ↔ q
to mean (p → q) ∧ (q → p). Similar to how proving
p ∧ q requires separate proofs of p and q, p ↔ q
requires separate proofs of p → q and q → p.
This means that to *prove a goal* of the form p ↔ q,
use `iff_intro` to separate the proof into two parts, one where
the goal is to prove p → q and one where the goal is to prove q → p."

Statement : x+2=3 ↔ x=1 := by
  iff_intro
  Hint "Use the `exact` tactic to resolve each of the two new goals."
  exact h1
  exact h2

NewTactic iff_intro

Conclusion ""
