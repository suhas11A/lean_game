/-
not as important, ok to deemphasize
skip discussion of how to use such asusmption, (also skipped in textbook)
consider upgrading example from above
-/

import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 9
Title "Unique Existential Quantifier"

Introduction ""

Statement : ∀ x ∈ ℤ, ∃! y ∈ ℤ, x+y=0 := by
  unique_exists

NewTactic

Conclusion ""
