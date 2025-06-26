import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 7
Title "Exercise"

Introduction "Try the exercise below."

-- TODO: how to handle Prop generally here
axiom property (x:X) (y:Y) :
Statement (X Y:Set) (p: property): (∃y:Y, ∀x:X, p x y) → (∀x:X, ∃y:Y, p x y) := by
  imp_intro h


NewTactic

Conclusion ""
