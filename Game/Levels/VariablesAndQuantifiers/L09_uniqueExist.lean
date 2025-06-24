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

Introduction "unique existential quantifier in the goal (skip in teh assumptions)"

Statement : ∀x:ℤ, ∃!y:ℤ, x+y=0 := by
  -- TODO: need unique_exists tactic
  unique_exists

NewTactic

Conclusion ""
