import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 6
Title "Exercise"

Introduction "Try the exercise below."

/-
unfold Not
∃y:ℤ, ∀x:ℤ, x+y=0 → False
h: ∃y:ℤ, ∀x:ℤ, x+y=0    False
h: ∀x:ℤ, x+y'=0         False


-/

Statement : ¬(∃y:ℤ, ∀x:ℤ, x+y=0) := by
  unfold Not
  imp_intro h
  exists_elim h with y', h
  forall_elim h of 0 into h0
  forall_elim h of 1 into h1
  rewrite [h0] at h1
  trivial


NewTactic

Conclusion ""
