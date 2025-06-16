import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 1
Title "Biconditional in the Hypothesis"

Introduction "todo"

Statement (h1:x=3) (h2:y=5) : x=3 ∧ y=5 := by
  and_intro
  Hint "asdf"

  exact h1
  Hint "asdf"

  exact h2

NewTactic

Conclusion "todo"
