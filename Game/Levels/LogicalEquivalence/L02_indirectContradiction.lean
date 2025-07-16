import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

World "LogicalEquivalence"
Level 2
Title "Indirect Proof by Contradiction (Double Negation)"


Introduction "Law of Double Negation: If p is a propositional variable, then p ≡ ¬¬p.
The law of double negation gives indirect proof by contradiction. In order to
prove a proposition p is true, it suffices to assume that p is false and derive a
contradiction. Prove the following theorem using indirect proof by contradiction. When
the goal is p, type `by_contra h`, to add hypothesis `h: ¬p` and change the goal to `False`."

Statement (x:ℕ) : x^2 < 2 → x < 2 := by
  intro h1
  by_contra h2
  Hint "Take a look at the theorem not_lt."
  rw [not_lt] at h2
  Hint "Take a look at the theorems `zero_le_two`, `pow_le_pow_left₀`, and `le_trans`.
  We need `have` to establish new assumptions in our proof. For example, write `have h5 : 2 ≤ 4 := by trivial`
  in order to add new hypotheses `h5 : 2 ≤ 4` and prove it by `trivial`. Note that if a theorem directly
  proves the hypotheses, we don't need `by`, just write the theorem name with any arguments after `:=`."
  have h3 : 0 ≤ 2 := zero_le_two
  have h4 : 4 ≤ x^2 := pow_le_pow_left₀ h3 h2 2
  have h5 : 2 ≤ 4 := by trivial
  have h6 : 2 ≤ x^2 := le_trans h5 h4
  rw [← not_lt] at h6
  contradiction

NewTheorem zero_le_two pow pow_le_pow_left₀ le_trans not_lt

Conclusion ""
