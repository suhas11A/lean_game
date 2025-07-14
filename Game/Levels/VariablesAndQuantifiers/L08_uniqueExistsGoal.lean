import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 8
Title "Proving uniquely existentially quantified statements"

Introduction "
The notation $∃!$ represents unique existential quantification.  The
formula $∃!x∈X, p(x)$ is short for $∃x∈X, (p(x) ∧ ∀y∈X, p(y) → y=x)$;
intuitively, this means that there is one, and only one, choice of
$x∈X$ such that $y=x$.

In Lean, we can unfold `ExistsUnique` to turn a formula with $∃!$ into
a formula in terms of the quantifiers and logical operators you
already know, but we can also use the `exists_unique_intro` and
`exists_unique_elim` tactics to work with $∃!$ directly.

The syntax for `exists_unique_intro` is `exists_unique_intro x`, where
`x` is the choice of $x∈X$ that satisfies $p(x)$.  When you use it,
the goal will change into two goals, one to show $p(x)$ and another to
show $∀y∈X, p(y) → y=x$.

This proof builds on level 5, but involves unique existential
quantification.  Try using `exists_unique_intro` to prove it.
"

/--
  For all integers $x$, there exists a unique integer $y$ such that $x+y=0$.
 -/
Statement : ∀ x : ℤ, ∃! y : ℤ, x+y=0 := by
  fix x
  exists_unique_intro -x
  simplify
  fix y
  assume h
  on_both_sides_of h, a becomes a-x
  simplify at h
  exact h

Conclusion ""

NewTactic exists_unique_intro
