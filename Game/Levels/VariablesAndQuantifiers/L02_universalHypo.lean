import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 1
Title "Universal Quantifier in the Hypothesis"

Introduction ""

Statement (h: ∀ x ∈ ℤ, x^2 ≥ 0) : (-5)^2 ≥ 0 := by
  forall_elim

NewTactic

Conclusion
