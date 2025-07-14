import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 9
Title "Using uniquely existentially quantified statements in proofs"

Introduction "
To use a uniquely existentially quantified assumption in our proof, we
use the `exists_unique_elim` tactic.  The syntax for
`exists_unique_elim` is `exists_unique_elim h into x, hexists,
hunique`, where `h` is an assumption of the form $∃!x∈X, p(x)$, `x` is
the choice of $x∈X$ that satisfies $p(x)$, `hexists` is the name of
the assumption that will prove $p(x)$, and `hunique` is the name of
the assumption that will prove $∀y∈X, p(y) → p(x)$.

In this exercise, we will use `exists_unique_elim` together with a
proof by contradiction.  This is more complicated than before, but we
will help you along the way!  Start by fixing $n∈ℤ$, assuming the
hypothesis, and using `exists_unique_elim` to get the unique $x$ such
that $nx=0$.
"

/--
  For all integers $n$, if there exists a unique number $x$ such that
  $nx=0$, then $n≠0$.
 -/
Statement : ∀ n : ℤ, (∃! x : ℤ, n * x = 0) → n ≠ 0 := by
  fix n
  assume h
  exists_unique_elim h into x, hex, hun
  Hint "
  Our goal is a negated statement, so use the `by_contra` tactic to
  prove it using proof by contradiction.
  "
  by_contra hn
  Hint "
  We now have assumed both that there exists a unique $x$ such that
  ${n}x=0$, and also that ${n}=0$.  The contradiction lies in the fact
  that there exist multiple such $x$ (in fact, any choice of $x$ works).
  "
  Hint "
  Use `forall_elim` with different choices of $y$ in `{hun}`, then use
  `have` and the assumption `{hn}` to prove that ${n}y=0$ for the
  choices of $y$ you picked.  Finally, use the resulting assumptions
  to show that $x$ is equal to two different numbers.
  "
  forall_elim hun of 0 into h0
  forall_elim hun of 1 into h1
  have h0' : n * 0 = 0 := by {rewrite [hn]; trivial}
  have h1' : n * 1 = 0 := by {rewrite [hn]; trivial}
  apply h0 at h0'
  apply h1 at h1'
  rewrite [← h0'] at h1'
  contradiction

Conclusion ""

NewTactic exists_unique_elim «have»
