-- provide more practice with intro and elim rules in more general setting


import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 7
Title "Exercise"

Introduction "Try the exercise below."

def is_sum_even (m n : Nat) : Prop
Statement (X Y:Set) (p: Prop X Y): (∃y:Y, ∀x:X, p x y) → (∀x:X, ∃y:Y, p x y) := by


NewTactic

Conclusion ""
