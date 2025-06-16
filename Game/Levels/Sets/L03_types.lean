import Game.Metadata
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Basic

World "Sets"
Level 3
Title "Basic example in intervals"

Introduction "
This level is to introduce the difference between Sets and Types in LEAN.
"
open Set
/-- What is a Type?. -/
Statement (U : Type)(x : U)(A : Set U)(h : x ∈ A): x ∈ A := by
  Hint "]
  In objects you can see `x : U` and `A : Set U` and what they mean is that x is an object of type `U`
  and A is an object of type `Set U` it means that A is a Set of elements of Type U.
  "
  Hint "
  In the previous 2 Levels, the elements were from either Set of Natural numbers
  or the Set or Real numbers."
  Hint "In LEAN Sets and Types are different, what it means is that `ℕ` is a typ and not a Set."
  Hint "`x : ℕ` means that x is of type `ℕ`."
  Hint "Now that we have realized `ℕ` is a type and not a Set, how do we get Set of all elements of Type `ℕ`."
  Hint "Set of all Natural numbers (Set of all elements of Type `ℕ`) is univ on type `ℕ`."
  Hint "`Set.univ : Set ℕ`, here `univ` is the set of Natural numbers."
  Hint "`evens : Set ℕ := ⦃n ∣ n % 2 = 0⦄`, here evens is a Set and not a type."
  Hint "Sets can only be pulled from a specific Type, you cant have a Set of all natural numbers and -1."
  Hint "In LEAN, the element `0 : ℕ` is different from `0 : ℝ`. If you wanted to have set of (1,π) then the element 1 can't be of type `ℕ` it has to be of the same type as π."
  Hint "Functions are defined from a type to another type not from a Set to another Set."
  exact h

Conclusion "--conc--"
NewTactic rfl
