import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 6
Title "Exercise"

Introduction "Try the exercise below."

Statement : ¬(∃y:ℤ, ∀x:ℤ, x+y=0) := by
  -- TODO : unfold Not
  imp_intro h
  exists_elim h into y', h'
  -- TODO: deal with the ℕ versus ℤ typing here, and add hints
  forall_elim h' of (0:ℤ) into h0
  forall_elim h' of (1:ℤ) into h1
  simp at h0
  rewrite [h0] at h1
  trivial


NewTactic

Conclusion ""
