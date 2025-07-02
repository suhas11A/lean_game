import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 4
Title "Existential Quantifier in the Hypothesis"

-- CONSIDERATION: have we established enough of a distinction between ∀E and ∃E?

Introduction "
If we have proven or assumed an existenatially quantified statement $∃x∈X,
p(x)$, then we can use it in our proofs with the elimination rule for
universal quantification:

(∃E) *If $∃x ∈ X, p(x)$ is true, and $q$ can be derived from the assumption that $p(a)$
is true for some fixed $a ∈ X$, then $q$ is true.*

This means that if our **assumption** is of the form $∃x ∈ X, p(x)$, then we
can take an $a ∈ X$ and assert that $p(a)$ is true.

When we have an assumption of the form `h : ∃x : X, p(x)`, we can
invoke ∃E and produce the new assumptions `a : X` and `h' : p(a)` by
typing `exists_elim h into a, h'`.  Try using `exists_elim` with the
correct syntax to begin the proof.
"

/--
  Given an integer $n$, if there exists an integer $q$ such that
  $n=4q$, then there exists an integer $p$ such that $n=2p$.
 -/
Statement : ∀ n:ℤ, (∃q:ℤ, n=4*q) → ∃p:ℤ, n=2*p := by
  fix n
  assume h
  exists_elim h into q', hq'
  exists_intro 2*q'
  rewrite [hq']
  rewrite [← Int.mul_assoc]
  trivial

NewTactic exists_elim

Conclusion ""
