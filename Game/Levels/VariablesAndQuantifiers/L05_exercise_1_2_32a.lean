/-
reinforce intro and elim rules for quantifiers
change p(x,y) prop to x+y=0

exercise 1.2.32a

-/

import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 5
Title "Exercise"

Introduction "Try the exercise below."

Statement : ∀x:ℤ, ∃y:ℤ, x+y=0 := by
  forall_intro x'
  exists_intro -x'
  trivial

NewTactic

Conclusion ""
