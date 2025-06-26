-- Exercise 1.2.32a except change p(x,y) to x+y=0
import Game.Metadata
import GameServer.Commands
import Mathlib.Tactic.Ring

World "VariablesAndQuantifiers"
Level 5
Title "Exercise"

-- CONSIDERATION : must address quantifiers in the order they appear, worth clarifying.

Introduction "The statement \"∀x ∈ X, ∃y ∈ Y, p(x,y)\" translates
to \"for any x in X, there exists a y in Y such that p(x,y) is true\". Note that the element y ∈ Y
such that p(x,y) is true is not necessarily the same for every x ∈ X. We choose x first then y, so
we must also invoke the proof strategies in that order, `forall_intro` then `exists_intro`. Try
this exercise on your own!"

Statement : ∀x:ℤ, ∃y:ℤ, x+y=0 := by
  forall_intro x'
  exists_intro -x'
  ring

NewTactic

Conclusion ""
