import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 5
Title "Implication in the Goal"

Introduction "Strategy 1.1.22 says if our goal is to prove p → q, then it suffices to assume
p is true and derive that q is true from this hypothesis. When our goal is of the form p → q,
we use the `intro` tactic to turn p into a hypothesis and leave q as the goal. Typing `intro h`
means to call our new hypothesis (p is true) h. Try this here to begin the proof."

Statement : x=3 → x=3 := by
  imp_intro h
  Hint "Use the `exact` tactic to finish the proof."
  exact h


NewTactic intro

Conclusion ""
