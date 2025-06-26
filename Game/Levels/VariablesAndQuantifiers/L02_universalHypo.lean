import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 2
Title "Universal Quantifier in the Hypothesis"

Introduction "
Let p(x) be a logical formula with free variable x with range X.
The elimination rule of the universal quantifier (∀) is

(∀E) If a ∈ X and ∀x ∈ X, p(x) is true, then p(a) is true.

This means that if our **assumption** is of the form `∀x ∈ X, p(x)`, then we
can take any a ∈ X and assert that p(a) is true.

When we have an assumption of the form `h: ∀x ∈ X, p(x)`, we can invoke ∀E
and produce the new assumptions `a:X` and `h': p(a)` by typing `forall_elim h of a into h'`.
Try using `forall_elim` with the correct syntax to begin the proof.
"

Statement (h: ∀ x : ℤ, x^2 ≥ 0) : (-5)^2 ≥ 0 := by
  forall_elim h of -5 into h1
  exact h1

NewTactic forall_elim
NewHiddenTactic «of»


Conclusion ""
