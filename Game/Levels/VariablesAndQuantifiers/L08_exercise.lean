/-
one more concerete and not so trivial example
take formulas from 1.3.34 (c,d) or 1.3.38
or its negation and ask sudents to prove on their own
-/

import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 7
Title "Exercise"

Introduction "Try the exercise below."

-- TODO: how to handle Prop generally here
Statement (X Y:Set) (p: property): (∃y:Y, ∀x:X, p x y) → (∀x:X, ∃y:Y, p x y) := by
  imp_intro h



∀x:ℝ, x>1 → (∃y:ℝ, (x<y ∧ ¬(x^2 ≤ y)))

NewTactic

Conclusion ""
