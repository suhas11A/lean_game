import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 7
Title "Exercise"

Introduction "Try the exercise below."

Statement (X Y : Type) (p : X → Y → Prop) : (∃ y : Y, ∀ x : X, p x y) → (∀ x : X, ∃ y : Y, p x y) := by
  -- TODO: check if proof correct, revise it, add hints
  imp_intro h
  forall_intro x'
  exists_elim h into y', hy'
  forall_elim hy' of x' into h1
  exists_intro y'
  exact h1

NewTactic

Conclusion ""
