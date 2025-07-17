import Game.Metadata
import GameServer.Commands

World "LogicalEquivalence"
Level 10
Title "Exercise"


Introduction ""

-- apply several logical equivalences to negate some formula, then prove
-- that the negation is true
-- something like exercise 1.18
-- not sure what process of neagting formula would look like
-- would need to introduce thms proved in previous levels and use them
-- could also add another practice level where students are asked to prove some
-- tautology like
-- ∀x ∈ X, [P(x) → Q(x)] ∨ [Q(x) → P(x)]
-- or (∀x ∈ X, P(x) ∨ Q(x) → ∀x ∈ X, P(x) ∨ ∃x ∈ X, Q(x))


/-
exercise 1.18
Let X be ℤ or ℚ and define a logical formula p by:
∀x ∈ X, ∃y ∈ X, (x<y ∧ [∀z ∈ X, ¬(x<z ∧ z<y)])
Write out ¬p as a maximally negated logical formula.
Prove that p is true when X = ℤ, and p is false when X = ℚ.
-/

example : ∀(x:ℤ), ∃(y:ℤ), (x<y ∧ ∀(z:ℤ), ¬(x<z ∧ z<y)) := by
  intro x
  use x+1
  constructor
  exact lt_add_one x
  intro z
  intro h1
  cases' h1 with h2 h3
  have h4 : z ≤ x := le_of_lt_add_one h3 -- error here !!!
  apply not_lt_of_ge at h4
  contradiction
