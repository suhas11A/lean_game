import Game.Metadata
import GameServer.Commands
import Mathlib.Tactic.Ring

World "VariablesAndQuantifiers"
Level 4
Title "Existential Quantifier in the Hypothesis"

-- CONSIDERATION: have we established enough of a distinction between ∀E and ∃E?

Introduction "
Let p(x) be a logical formula with free variable x with range X.
The elimination rule of the existential quantifier (∃) is

(∃E) If ∃x ∈ X, p(x) is true, and q can be derived from the assumption that p(a)
is true for some fixed a ∈ X, then q is true.

This means that if our **assumption** is of the form `∃x ∈ X, p(x)`, then we
can take an a ∈ X and assert that p(a) is true.

When we have an assumption of the form `h: ∃x ∈ X, p(x)`, we can invoke ∃E
and produce the new assumptions `a:X` and `h': p(a)` by typing `exists_elim h into a, h'`.
Try using `exists_elim` with the correct syntax to begin the proof.
"

Statement (n:ℤ) (h: ∃q:ℤ, n=4*q) : ∃p:ℤ, n=2*p := by
  exists_elim h into q', hq'
  exists_intro 2*q'
  -- TODO: revise proof
  rewrite [hq']
  ring

NewTactic exists_elim ring

Conclusion ""
