import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 4
Title "Disjunction in the Goal"

Introduction "The two introduction rules of the disjunction operator are as follows:

(∨I₁) If p is true, then p ∨ q is true.
(∨I₂) If q is true, then p ∨ q is true.

In this level, we invoke ∨I₁ using the `or_intro` tactic.
If we have a goal of the form p ∨ q, we write `or_intro p` to specify that
we will complete the proof by showing that p is true.
Here, type `or_intro x=3` to begin the proof."

Statement (h:x=3) : x=3 ∨ y=5 := by
  or_intro x=3
  Hint "Use the `exact` tactic to finish the proof."
  exact h

NewTactic or_intro

Conclusion ""
