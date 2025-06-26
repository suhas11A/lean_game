-- Exercise 1.2.32a except change p(x,y) to x+y=0
import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 5
Title "Exercise"

Introduction "Try the exercise below."

Statement : ∀x:ℤ, ∃y:ℤ, x+y=0 := by

  -- QUESTION / THOUGHT : in math (and prob lean as well) you have to address the quantifiers
  -- in the order they appear, so first you pick x then your y is based on the chosen x
  forall_intro x'
  exists_intro -x'

  -- TODO: finish pf

NewTactic

Conclusion ""
