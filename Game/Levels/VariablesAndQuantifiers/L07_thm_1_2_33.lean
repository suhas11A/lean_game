import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 7
Title "Exercise"

Introduction "
The previous two examples illustrate a general theorem in
propositional logic: “for all $x$, there exists $y$ ...” is a weaker
statement than “there exists $y$ such that for all $x$ ...”.

The intuition behind this statement is that when “for all” is in
front, we are allowed to pick a different $y$ for each value of $x$,
but when “there exists” is in front, we have to start by picking a
single value of $y$, and prove that it works for all $x$.  So, “for
all $x$, there exists $y$” is easier to prove, but “there exists $y$
such that for all $x$” says more.

Formally, what we want to show is, given a proposition $p$ over
variables $x∈X$ and $y∈Y$, that $∃y∈Y,∀x∈X,p(x,y)$ implies
$∀x∈X,∃y∈Y,p(x,y)$.  The proof in pen-and-paper mathematics is
straightforward.  By our assumption, we have $b∈Y$ such that for all
$x$, $p(x,b)$ holds, so for any given value of $x$, we may choose
$y=b$ as the witness to $∃y∈Y, p(x,y)$.  Your job is to translate this
into Lean.

Note: in Lean, we write `p : X → Y → Prop` in order to show that `p`
is a proposition that references an `X` and a `Y`.
"

/--
  Let $p$ be a logical formula parametrized over variables $x∈X$ and
  $y∈Y$.  If there exists $y∈Y$ such that for all $x∈X$, $p(x,y)$
  holds, then for all $x∈X$, there exists $y∈Y$ such that $p(x,y)$
  holds.
  -/
Statement (X Y : Type) (p : X → Y → Prop) : (∃ y : Y, ∀ x : X, p x y) → (∀ x : X, ∃ y : Y, p x y) := by
  assume h
  fix x'
  exists_elim h into y', hy'
  forall_elim hy' of x' into h1
  exists_intro y'
  exact h1

NewTactic

Conclusion ""
