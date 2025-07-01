import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 6
Title "Exercise"

Introduction "
Remember how we said in the previous exercise that if you reversed the
order of the quantifiers, the statement would no longer be true?  In
this exercise, your job is to prove that.

There are multiple ways to proceed with this proof, but you will need
to use proof by contradiction and end up with a conclusion that says
that two different numbers are equal—say, $0=1$.  From there, use
`contradiction` to end the proof.
"

/--
  There does not exist $y∈ℤ$ such that, for all $x∈ℤ$, $x+y=0$.
  -/
Statement : ¬(∃y:ℤ, ∀x:ℤ, x+y=0) := by
  by_contra h
  exists_elim h into y', h'
  forall_elim h' of 0 into h0
  forall_elim h' of 1 into h1
  rewrite [zero_add] at h0
  rewrite [h0] at h1
  contradiction

Conclusion ""
