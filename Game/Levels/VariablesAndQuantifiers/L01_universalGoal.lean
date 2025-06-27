import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

World "VariablesAndQuantifiers"
Level 1
Title "Universal Quantifier in the Goal"


Introduction "
Consider a logical formula $p(x)$ parametrized over a variable $x$
with domain of discourse $X$.  The formula $∀x∈X, p(x)$ ($∀$ is typed
as `\\forall` and read as “for all”) expresses that $p(x)$ holds
whenever $x$ is an element of $X$.  We say that this kind of formula
is *universally quantified*.

For instance, $∀n∈ℤ, n<n+1$ means that every integer is less than
itself plus one.  This is obviously true; how do we prove it?

To prove a goal of the form $∀x ∈ X, p(x)$, we use the following strategy:

(∀I) *If $p(x)$ can be derived from the assumption that $x$ is an arbitrary
element of $X$, then $∀x ∈ X, p(x)$.*

By arbitrary, we mean that we assume nothing about $x$ other than that
it is an element of $X$.  In particular, we can’t assume that it is
any *particular* element of $X$.  When we prove $∀n∈ℤ, n<n+1$, we will
introduce a new integer $n$, but we won't know what $n$ actually is,
since our proof must work for every possible $n∈ℤ$.

To prove a universally quantified statement in Lean, use the
`forall_intro` tactic.  Typing `forall_intro y` invokes ∀I by taking
$y$ to be an arbitrary element of the domain of discourse and changing
the goal to proving that $p(y)$ is true.  (You can use whatever
variable name you want instead of `y`.)  Try using `forall_intro` with
the correct syntax to begin the proof.
"

/-- For all integers $n$, $n$ is less than $n+1$. -/
Statement : ∀n:ℤ, n<n+1 := by
  forall_intro y
  Hint "
  Observe that `{y}` has been added as a new object, and that the goal
  has changed to `{y} < {y} + 1`—`n` has been replaced with `{y}`.  To
  finish the proof, we can use `simp`.
  "
  simp

NewTactic forall_intro
Conclusion "
If you haven’t noticed, we use the $∈$ symbol (`\\in`, read `in`) with
$∀$ in convential math notation, but in Lean, we use a colon instead:
`∀n : ℤ, n < n + 1`.
"
