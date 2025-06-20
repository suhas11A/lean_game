import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 6
Title "Implication in the Hypothesis"

Introduction "Use the information provided in the
previous level to complete this proof on your own!"

Statement (h1: x=3 → y=5) (h2: x=3) : y=5 := by
  imp_elim h1 with h2 into h3
  Hint "Use the `exact` tactic to finish the proof."
  exact h3

NewTactic imp_elim

Conclusion ""
