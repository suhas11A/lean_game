import Game.Metadata
import GameServer.Commands
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

World "LogicalEquivalence"
Level 2
Title "Indirect Proof by Contradiction (Double Negation)"


Introduction ""


Statement (a b c : ℝ) : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a^2+b^2=c^2 → a+b ≥ c := by
  intro h
  and_elim h into h1, h2, h3, h4
  by_contradiction h' -- suppose a + b < c
  -- a^2 + b^2 ≤ a^2 + 2ab + b^2 = (a+b)(a+b) < c^2, contradiction
  /-
  requires a lot of arithmetic which is tedious in lean
  could also teach students how to apply previous theorems, but maybe too much to throw
  at them at once. should be focusing on the proof strategy here
  conclusion for now: save this as a later example, choose something simpler, maybe
  with general propositional variables
  -/



NewTactic

Conclusion
