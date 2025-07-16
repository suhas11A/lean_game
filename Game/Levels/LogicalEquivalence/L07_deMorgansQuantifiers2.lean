import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 7
Title "De Morgan's Law for Quantifiers, Part 2"

Introduction ""

theorem deMorg (p : X → Prop) : (∀(x:X), ¬(p x)) ↔ ¬(∃(x:X), p x) := by
  constructor
  intro h1
  unfold Not
  intro h2
  cases' h2 with x h2
  have h3 : ¬p x := by apply h1
  contradiction
  intro h
  intro x
  unfold Not
  intro hp
  have h1 : ∃x, p x := by use x
  contradiction

theorem double_negation_elimination {p : Prop} (h : ¬¬p) : p := by
  by_cases hp : p
  exact hp
  contradiction

theorem double_negation_elimination' {X} {x:X} (p : X → Prop) : ¬¬p x ↔ p x := by
  sorry

example (p : X → Prop) : ¬(∀(x:X), p x) ↔ (∃(x:X), ¬p x) := by
  constructor
  intro h
  apply double_negation_elimination
  rw [← deMorg]
  rewrite [double_negation_elimination' p]


Conclusion ""
