import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 2
Title "Universal Quantifier in the Hypothesis"

Introduction "
If we have proven or assumed a universally quantified statement $∀x∈X,
p(x)$, then we can use it in our proofs with the elimination rule for
universal quantification:

(∀E) *If $a ∈ X$ and $∀x ∈ X, p(x)$ is true, then $p(a)$ is true.*

This means that if our **assumption** is of the form $∀x ∈ X, p(x)$,
then we can take any particular $a ∈ X$ and assert that $p(a)$ is
true.  Note that we have to decide on a specific $a$ to use.

When we have an assumption of the form `h: ∀x : X, p(x)`, and either
an object `a:X` or an expression `a` that is a valid `X`, we can
invoke ∀E and produce the new assumption `h': p(a)` by typing:

`forall_elim h of a into h'`

Keep in mind, you can’t just type in `a`; you have to provide the
specific element of `X` that you want in place of it.

You’ll need to use `forall_elim` twice during this proof.
"

/--
  Let $p(x)$ and $q(x)$ be propositions defined on the natural
  numbers.  If, for all $x∈ℕ$, $p(x)$ is true, and for all $x∈ℕ$,
  $q(x)$ is true, then for all $x∈ℕ$, the formula $p(x)∧q(x)$ is true.
  -/
Statement (p q : ℕ → Prop)
  : (∀ x : ℕ, p x) ∧ (∀ x : ℕ, q x) → (∀ x : ℕ, p x ∧ q x) := by
  assume h
  and_elim h into h1, h2
  fix x
  and_intro
  forall_elim h1 of x into h1'
  exact h1'
  forall_elim h2 of x into h2'
  exact h2'

NewTactic forall_elim
NewHiddenTactic «of»


Conclusion ""
