-- Exercise 1.2.32a except change p(x,y) to x+y=0
import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 5
Title "Exercise"

Introduction "
Pay attention to the order of quantifiers in this exercise.  Because
$x$ is bound before $y$, the choice of $y$ in the proof can depend on
the value of $x$.  If we were to reverse the order of the quantifiers,
this statement would not be true; there is no *single* value of $y$
such that for all $x∈ℤ$, $x+y=0$.

We first fix $x$ and then choose $y$, so we must also invoke the
proof strategies in that order: `forall_intro` and then
`exists_intro`.  Try this exercise on your own!
"

/--
  For all integers $x$, there exists an integer $y$ such that $x+y=0$.
 -/
Statement : ∀x:ℤ, ∃y:ℤ, x+y=0 := by
  fix x
  exists_intro -x
  apply Int.add_right_neg

Conclusion ""
