import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 3
Title "De Morgan's Law for Operators"



Statement (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  unfold Not
  intro h
  by_cases hp : p
  right
  intro hq
  rw [and_imp] at h
  apply h at hp
  apply h at hq
  exact hq
  left
  unfold Not at hp
  exact hp
  unfold Not
  intro h
  cases' h with h1 h2
  rw [amd_imp]
  intro hp
  intro hq
  apply h1 at hp
  exact hp
  rw [and_imp]
  intro hp
  intro hq
  apply h2 at hq
  exact hq
