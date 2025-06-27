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

/-
∃! y : ℤ, x'+y=0
unique_exists_intro
-/

Introduction ""

Statement : ∀ x : ℤ, ∃! y : ℤ, x+y=0 := by
  forall_intro x'
  unique_exists_intro

NewTactic

Conclusion ""
