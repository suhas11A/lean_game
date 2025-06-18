import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 3
Title "Existential Quantifier in the Goal"


Introduction "Definition 1.2.17 states if p(x)
is a logical formula with free variable x with range X,
then ∃ x ∈ X, p(x) is the logical formula with
introduction rule: If a ∈ X and p(a) is true, then ∃ x ∈ X, p(x).
We can invoke the introduction rule of the existential quantifier
with the `exists_intro` tactic. When we have a statement of the form
∃ x ∈ X, p(x) for some logical formula p(x) as our goal, we write `exists_intro x₀`
to mean x₀ ∈ X and p(x₀) is true, so replace the goal with p(x₀), as it remains that
p(x₀) is indeed true. Determine which natural number n we should use to prove the statement at
right, and type `exists_intro n` to begin the proof."

Statement (h: x=1) : ∃ n : ℕ, x=n+1 := by
  exists_intro 0
  Hint "Now use the `rw` tactic to rewrite the right side of the equation x=0+1."
  rw [zero_add]
  Hint "Finish off the proof!"
  exact h


NewTactic exists_intro

Conclusion ""
