import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 1
Title "Universal Quantifier in the Hypothesis"

Introduction "
Let p(x) be a logical formula with free variable x with range X.
The elimination rule of ∀ is
(∀E) If a ∈ X and ∀x ∈ X, p(x) is true, then p(a) is true.

"

Statement (h: ∀ x : ℤ, x^2 ≥ 0) : (-5)^2 ≥ 0 := by
  forall_elim h of -5 into h1
  exact h1




NewTactic

Conclusion
