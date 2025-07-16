import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 4
Title "De Morgan's Law for Operators, Part 1"

Introduction "Try beginning to prove De Morgan's Law for Operators!"

Statement (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  unfold Not
  intro h

  Hint "Our first statement to prove is that if p ∧ q is false, then
  either p is false or q is false. The way we prove this is by invoking the law of the excluded middle,
  which is that p ∨ ¬p is always true. Essentially, we must split our proof into two cases:
  (1) p is true; (2) p is false. Typing `excluded_middle p as hp` adds hypothesis `hp: p ∨ ¬p`."

  excluded_middle p as hp
  or_elim hp into h1, h2
  right
  rewrite [and_imp] at h
  apply h at h1
  exact h1
  left
  unfold Not at h2
  exact h2

  unfold Not
  intro h
  or_elim h into hp, hq
  rewrite [amd_imp]
  intro h1
  intro h2
  apply hp at h1
  exact h1
  rewrite [and_imp]
  intro hp
  exact hq

NewTactic by_cases excluded_middle
Conclusion ""
