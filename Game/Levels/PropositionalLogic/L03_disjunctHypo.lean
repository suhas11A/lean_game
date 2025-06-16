import Game.Metadata
import GameServer.Commands


World "PropositionalLogic"
Level 3
Title "Disjunction in the Hypothesis"

Introduction "todo"

Statement (h:x=3 ∨ y=5) : y=5 := by
  or_elim h into hx, hy
  Hint "asdf"

  exact h1
  Hint "asdf"

  exact h2

NewTactic

Conclusion "todo"
