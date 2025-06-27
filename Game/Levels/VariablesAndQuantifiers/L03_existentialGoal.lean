import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 3
Title "Existential Quantifier in the Goal"


Introduction "
For a logical formula $p(x)$ parametrized over $x∈X$, the formula
$∃x∈X, p(x)$ ($∃$ is typed `\\exists` and read “there exists…such
that”) expresses that there is a particular $a∈X$ such that $p(a)$
holds.  We say that such a formula is *existentially quantified*.

For instance, $∃n∈ℤ, n^2 = 2n$ is read “there exists an integer $n$
such that $n$ squared equals two times $n$”.  In order to prove such a
statement, we must use the introduction rule for existential
quantification:

(∃I) *If $a ∈ X$ and $p(a)$ is true, then we can conclude $∃x ∈ X, p(x)$.*

In other words, we must give a particular $a∈X$ and prove that $p(a)$
holds to conclude $∃x∈X, p(x)$.  Here, $a$ is often called a *witness*
to the statement $∃x∈X, p(x)$.  Note that some choices of the witness
may be incorrect; for instance, we cannot pick $n=3$ as a witness for
$∃n∈ℤ, n^2 = 2n$, since $3^2=9$ but $2(3)=6$.  And there may be
multiple different correct choices of a witness; the previously
mentioned proposition has two correct witnesses, and either will
suffice to prove it.

In Lean, if we have a goal of the form `∃x ∈ X, p(x)`, we can use
`exists_intro y`, where y is an element of X, to change the goal into
p(y).  Try using `exists_intro` in this proof.
"

/--
  There exists an integer $n$ such that $n^2=2n$.
 -/
Statement : ∃n : ℤ, n^2 = 2*n := by
  -- todo: there is an ugly ↑ as a result of having to coerce 2 from ℕ to ℤ.
  -- Is there a way to get rid of this?
  exists_intro 2
  Hint "Use the `trivial` tactic to finish the proof."
  trivial

NewTactic exists_intro

Conclusion ""
