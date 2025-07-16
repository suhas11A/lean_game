import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 6
Title "De Morgan's Law for Quantifiers, Part 1"

Introduction "Try proving De Morgan's Law for Quantifiers on your own!"

Statement (p : X → Prop) : (∀(x:X), ¬(p x)) ↔ ¬(∃(x:X), p x) := by
  constructor
  intro h1
  unfold Not
  intro h2
  exists_elim h2 into x, h2
  have h3 : ¬p x := by apply h1
  contradiction
  intro h
  intro x
  unfold Not
  intro hp
  have h1 : ∃x, p x := by use x
  contradiction


NewTactic use

Conclusion ""
