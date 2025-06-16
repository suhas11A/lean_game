import Game.Metadata
import GameServer.Commands

World "PropositionalLogic"
Level 6
Title "Implication in the Hypothesis"

Introduction "todo"

Statement (h: x=3 → y=5) (h1: x=3) : y=5 := by
  apply h at h1
  exact h1

NewTactic

Conclusion "todo"
