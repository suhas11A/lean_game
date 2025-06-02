import GameServer.Commands
import Mathlib.Tactic.Ring

World "LogicalStructure"
Level 1
Title "Introduction to Proofs in Lean"

Introduction "
Following along with Example 1.1.1, let's prove a basic theorem within Lean.

In the center window, you can see the statement of the theorem you
need to prove, along with a list of “Objects” and a “Goal”.  The
objects tell you which variables exist, and what type they are.  In
this case, $a$, $b$, and $c$ are all members of the type $ℤ$, the
integers.  The goal is what you have left to prove.

The text window at the bottom allows you to enter commands, called
tactics, that advance the proof.  There is a list of tactics on the
right side of the screen.  Clicking on a tactic will give you a
description of it.

To start, we should give names to the hypotheses of the theorem, that
$c ∣ b$ and that $b ∣ a$.  Type `intro c_div_b` to give the first
hypothesis a name.
"

/-- Let $a$, $b$, $c \in \mathbb{Z}$.  If $c$ divides $b$ and $b$
    divides $a$, then $c$ divides $a$. -/
Statement (a b c : Int) : c ∣ b → b ∣ a → c ∣ a := by
  intro c_div_b
  Hint "
  Notice that there is a new section, Assumptions, that lists the
  facts that we have learned so far.  `c_div_b` is the name of the
  assumption that says that $c ∣ b$.  Also notice that the goal has
  changed; since we have introduced the first hypothesis, it was
  removed from our goal.

  Type `intro b_div_a` in order to introduce the second hypothesis.
  "
  intro b_div_a
  Hint "
  Now the only thing we have left to do is to show that $c ∣ a$.
  Following the book, let’s expand the definition of “divides” in our
  hypotheses.  To do this, we can use the `rcases` tactic, like so:
  ```
  rcases c_div_b with ⟨q, hb⟩
  ```
  We will see more clearly what rcases does in the future, but for
  now, think of it as a way to expand the meaning of a hypothesis by
  spliting it into smaller objects and hypotheses.  What do you expect
  $q$ and `hb` will stand for?
  "
  rcases c_div_b with ⟨q, hb⟩
  Hint "
  We see that $q$ is introduced as a new integer, and we have a new
  hypothesis, `hb` which tells us that $b=qc$.  Try to expand the
  definition of `b_div_a` on your own; use $r$ for the name of the
  witness.
  "
  rcases b_div_a with ⟨r, ha⟩
  Hint "
  Our next step is to substitute $b$ for $qc$ in the equation $a=rb$.
  We can do this using the `rw` tactic, short for “rewrite”.  To use
  `rw`, type
  ```
  rw [hb] at ha
  ```
  The hypothesis within the square brackets says what will be
  rewritten, and the hypothesis after the keyword `at` says where to
  perform the substitution.  When you use this tactic, Lean will
  replace the first occurrence of the left-hand side of `hb` (i.e.,
  $q$) with the right-hand side of `hb` (i.e., $qc$) in the equation
  `ha`.
  "
  rw [hb] at ha
  Hint "
  We have made some progress, but we still need to prove our goal.  In
  order to prove $a ∣ c$, we have to find an integer $s$ such that $a
  = sc$.  The integer $s$ that we choose is called a *witness* to $a ∣
  c$, and we need to tell Lean what the value of $s$ is.

  We can do this using the `use` tactic.  Type
  ```
  use r * q
  ```
  to tell Lean that the witness to $a ∣ c$ is $rq$.
  "
  use r * q
  Hint "
  Now, since Lean knows what the witness is, our goal has changed to
  proving that $a = c(rq)$.  We have a hypothesis that tells us what
  $a$ is, so we can replace $a$ in our goal with its expansion by
  again using the `rw` tactic.  This time, type
  ```
  rw [ha]
  ```
  There’s no `at` in this command; this means that Lean will do its
  rewriting in the goal, rather than in another hypothesis.
  "
  rw [ha]
  Hint "
  Oh no—we’re so close now, but Lean seems to have tripped up on
  something basic, probably so simple you didn’t even think about it.
  We need to use associativity of multiplication to finish this proof.

  Lean doesn’t know about basic properties of addition and
  multiplication, because they are theorems, and they have to be
  proven first.  Later on, we will do the work of proving these
  properties ourselves, but for now, there is a tactic that can apply
  these properties for us, called `ring`.  Type in `ring`, on its own,
  to finish the proof.
  "
  ring

NewTactic intro rcases rw use ring


Conclusion "todo"
