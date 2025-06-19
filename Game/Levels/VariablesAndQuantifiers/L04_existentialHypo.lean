import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 4
Title "Existential Quantifier in the Hypothesis"

Introduction "
Let p(x) be a logical formula with free variable x with range X.
Definition 1.2.17 states ∃x ∈ X, p(x)
is the logical formula defined according to the following introduction and elimination rule:

(∃I) If a ∈ X and p(a) is true, then ∃x ∈ X, p(x).
(∃E) If ∃x ∈ X, p(x) is true, and q can be derived from the assumption that p(a)
is

Definition 1.2.17 states the elimination rule of the existential quantifier
is: If \"∃ x ∈ X, p(x)\" is true, and q can be derived from
the assumption \"p(a) is true for some fixed a ∈ X\", then q is true,
which is invoked with the `exists_elim` tactic.
Strategy 1.2.24 rephrases the elimination rule more intuitively,
explaining that if we have a hypothesis \"∃x ∈ X, p(x),\" then we
can introduce a variable a ∈ X and assume p(a) is true. We use
`exists_elim h int"

Statement (n:ℤ) (h: ∃q:ℤ, n=4*q) : ∃p:ℤ, n=2*p := by
  exists_elim h into q', hq'
  exists_intro 2*q'
  rw [two_mul_two_eq_four]
  exact hq


NewTactic exists_elim

Conclusion ""
