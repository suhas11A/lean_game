import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Basic

World "SetOperations"
Level 5
Title "Basic example in intervals"

Introduction "
Following along with Example 2.1.17.

To prove the goal
"
def evens : Set ℕ := { n | n % 2 = 0 }
def odds : Set ℕ := { n | n % 2 = 1 }

open Set
/-- Let X, Y and Z be sets. Prove that X∩(Y∪Z) = (X∩Y)∪(X∩Z). -/
Statement : Set.univ \ evens = odds := by
  apply Subset.antisymm
  intro n hn
  rw[mem_diff] at hn
  cases Nat.mod_two_eq_zero_or_one n
  have h1 : n ∈ evens := h
  have a_1 := hn.2
  contradiction
  have h1 : n ∈ odds := h
  exact h1
  intro n hn
  have h1 : n % 2 = 1 := hn
  have h2 : 1 ≠ 0 := Nat.one_ne_zero
  rw[← h1] at h2
  have h3 : n ∉ evens := h2
  have h4 : n ∈ (Set.univ : Set ℕ) := trivial
  exact And.intro h4 h3


Conclusion "--conc--"


NewTheorem Set.mem_union lt_trans and_or_left Nat.mod_two_eq_zero_or_one Set.mem_diff Set.univ Nat.one_ne_zero
NewTactic trivial contradiction
