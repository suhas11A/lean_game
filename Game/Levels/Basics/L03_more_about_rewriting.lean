import Game.Metadata
import Init.Prelude

World "Basics"
Level 3
Title "More about rewriting"

Introduction "
To explore some more of Lean’s features, let’s prove the same theorem
as before, but in a different way.

Start by introducing the hypotheses as before.  You can do both at
once by typing `intro hx hy`; in general, you can type as many space
separated names as there are hypotheses to assume.
"

/-- For natural numbers $x$ and $y$, if $x=3$ and $y=3$, then $x=y$. -/
Statement (x y : ℕ) : x = 3 → y = 3 → x = y := by
  intro hx hy
  Hint "
  Now, try writing the command `rewrite [← {hx}] at {hy}`.
  "
  rewrite [← hx] at hy
  Hint "
  What exactly did that do?  The new syntax here is `at`; it tells
  Lean to do whatever it would have done to the goal to an assumption
  instead.  `rewrite [← {hx}]` would replace `3` with `{x}` in the
  goal, so `rewrite [← {hx}] at {hy}` replaces `3` with `{x}` in the
  equation for `{hy}`.
  "
  Hint "
  Now `{hy}` and our goal look very similar!  ... almost.  The goal is
  backwards, but we can get them to line up by using the `symm`
  tactic, which flips an equality in the goal.  Try typing `symm`.
  "
  symm
  Hint "
  Can you guess what `symm at {hy}` would have done?
  "
  Hint "
  Since the goal now exactly matches one of our assumptions, we can
  tell Lean to close off the proof just by using the tactic
  `assumption`.  Try typing `assumption` now.
  "
  assumption

/--
  `symm` turns a goal of the form `a = b` into `b = a`.

  `symm at h` does the same for an assumption `h`.
  -/
TacticDoc symm

/--
  `assumption` clears the current goal if it matches one of the
  assumptions.
  -/
TacticDoc assumption

NewTactic symm assumption

Conclusion "

"
