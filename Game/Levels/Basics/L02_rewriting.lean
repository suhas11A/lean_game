import GameServer.Commands
import Mathlib.Init.Data.Nat.Notation

World "Basics"
Level 2
Title "Implications and the rewrite tactic"

Introduction "
Let us prove another simple theorem.  This is again obvious, but the
structure of the proof is more complicated than before.

We now are dealing with mathematical *objects*, which are listed in
the middle of the screen above the goal.  There are two objects: $x$
and $y$, and both of them are of *type* `ℕ`, which means that $x$ and
$y$ are natural numbers.

The notion of a type is specific to Lean; it tells you what kind of
object something is, such as a natural number, integer, or function.
Writing `x : ℕ` is close to saying $x∈ℕ$ in pen-and-paper mathematics,
but they are not exactly the same; you will see more in Chapter 2.

The goal is more interesting; it takes the form of an implication.
Here we see that we must prove that $x = 3$ and $y = 3$ together imply
$x = y$.

When we want to prove a theorem like this in standard mathematics, we
must first assume that the hypotheses hold, by saying, “Assume $x = 3$
and assume $y = 3$.”  Similarly, in Lean, we must first assume that
the hypotheses hold by using the tactic `intro`.

Type `intro hx` to assume the first hypothesis, that $x = 3$.  Here,
`hx` is the name you will give to the hypothesis; you can pick
anything you want.
"

/-- For natural numbers $x$ and $y$, if $x=3$ and $y=3$, then $x=y$. -/
Statement (x y : ℕ) : x = 3 → y = 3 → x = y := by
  intro hx
  Hint "
  Notice that there is a new section in the middle of the screen,
  titled “Assumptions.”  This lists all the hypotheses that you have
  assumed to be true.  Here, we just have one; $x = 3$, and its name
  is `{hx}`.
  "
  Hint "
  Also, the goal has been changed.  Since we assumed $x = 3$, what we
  have left to show is that $y = 3 ⇒ x = y$, and the goal keeps track
  of this for us by removing the first hypothesis.
  "
  Hint "Proceed with `intro hy` in order to assume the second hypothesis."
  intro hy
  Hint "
  We now have assumed both hypotheses and are ready to prove the
  conclusion.  Using `rfl` here won’t work though, since Lean sees
  `{x}` and `{y}` as two different objects.  We need to adjust the
  goal to something we can prove using `rfl`.
  "
  Hint "
  To do this, we will introduce a new tactic, `rewrite`.  This takes
  the name of an assumption giving an equality, finds the first place
  where the left-hand side is in the goal, and replaces it with the
  right-hand side.  Type `rewrite [{hx}]` to change the `{x}` in the
  goal into a `3`.  The brackets are important; don't leave them out.
  "
  rewrite [hx]
  Hint "
  For ${y}$, we’ll use `rewrite` in a slightly different way.  By
  typing `←` (you can type this by typing `\\leftarrow`; it will
  automatically convert to the left arrow symbol for you) before the
  name of an assumption, Lean will look for the right-hand side in the
  goal and replace it with the left-hand side.

  Try `rewrite [← hy]` to see what it does.
  "
  rewrite [← hy]
  Hint "
  `rewrite` looked for `3` in the goal, and replaced it with `y`.

  Now, we can prove the goal trivially using `rfl`, because both sides
  are the same.
  "
  rfl

/--
  `intro <name> <name> ...` assumes/fixes one or more
  hypotheses/variables.  You can give each hypothesis and variable any
  name you want, and you can introduce multiple at once by placing
  spaces between the names.
  -/
TacticDoc intro

/--
  If `h` stands for an equality `x = y`, then `rewrite [h]` will
  replace the first occurrence of `x` in the goal with `y`, and
  `rewrite [← h]` will replace the first occurrence of `y` in the goal
  with `x`.

  If `g` is a hypothesis in the Assumptions block, then `rewrite [h]
  at g` will replace `x` with `y` in the formula for `g`.
  -/
TacticDoc rewrite

NewTactic intro rewrite

Conclusion "

"
