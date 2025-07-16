import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 5
Title "De Morgan's Law for Operators, Part 2"


Introduction "Try completing this exercise on your own!"

Statement : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  unfold Not
  intro h
  excluded_middle p as hp
  right
  rw [and_imp] at h
  apply h at hp
  exact hp
  left
  unfold Not at hp
  exact hp
  unfold Not
  intro h
  or_elim h into h1, h2
  rw [and_imp]
  intro hp
  apply h1 at hp
  trivial
  rw [and_imp]
  intro hp
  exact h2

Conclusion ""
