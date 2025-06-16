import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 4
Title "Disjunction in the Goal"

Introduction "Definition 1.1.12 gives the three properties of the disjunction operator.
In this level, we will invoke the first property: If p is true, then p ∨ q is true.
When the goal of our proof has a disjunction ∨ as its outermost operator, we use the `or_intro`
tactic to separate the goal into two separate goals. If we want to prove p ∨ q, it suffices to
prove either p is true or q is true. If we want to prove that p is true, we would type `or_intro p`.
Here, type `or_intro x=3` to begin the proof."

Statement (h:x=3) : x=3 ∨ y=5 := by
  or_intro x=3
  Hint "Use the `exact` tactic to finish the proof."
  exact h

NewTactic or_intro

Conclusion ""
