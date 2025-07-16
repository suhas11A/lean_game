import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

World "LogicalEquivalence"
Level 3
Title "Proof by Contraposition"

Introduction "A **contrapositive** of a proposition of the form
p → q is the proposition ¬q → ¬p.The Law of Contraposition states
if p and q are propositional variables, then p → q ≡ (¬q) → (¬p).
Prove the following theorem using proof by contraposition, which is applied
using the `contrapose` tactic."


Statement (n m : ℕ) : m*n > 64 → m > 8 ∨ n > 8 := by
  contrapose
  Hint "Take a look at theorems that may help complete the proof. Remember to
  use `rw` or `rewrite` and `repeat rw` when a theorem needs to be applied multiple times."
  rw [not_or]
  repeat rw [not_lt]
  rw [and_imp]
  intros hm hn
  apply Nat.mul_le_mul at hn
  apply hn at hm
  rewrite [mul_comm]
  exact hm

NewTactic contrapose
NewTheorem not_or not_lt and_imp Nat.mul_le_mul mul_comm

Conclusion ""
