import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 6
Title "De Morgan's Law for Quantifiers"

Introduction "Try proving De Morgan's Law for Quantifiers on your own!"

Statement (p : X → Prop) : (∀(x:X), ¬(p x)) ↔ ¬(∃(x:X), p x) := by
  constructor
  · intro h1
    unfold Not
    intro h2
    exists_elim h2 into x', hx'
    forall_elim h1 of x' into h1'
    apply h1' at hx'
    exact hx'

  unfold Not
  intro h1
  fix x'
  intro px

  have h : (∃x:X, p x)



  apply h1 at h
  exact h
