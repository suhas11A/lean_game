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
  Hint "
  In objects feild you can see `x : U` and `A : Set U` and what they mean is that x is an object of type `U`
  and A is an object of type `Set U` it means A is a Set of elements of Type U.
  "
  Hint "
  In the previous 2 Levels, the elements were from either of type Natural numbers
  or of type Real numbers."
  Hint "In LEAN Sets and Types are different, what it means is that `ℕ` is a type and not a Set."
  Hint "`x : ℕ` means that x is of type `ℕ`."
  Hint "Now that we have realized `ℕ` is a type and not a Set, how do we get Set of all elements of Type `ℕ`."
  Hint "Set of all Natural numbers (Set of all elements of Type `ℕ`) is univ on type `ℕ`."
  Hint "`univ : Set ℕ`, here `univ` is the set of Natural numbers."
  Hint "`evens : Set ℕ := ⦃n ∣ n % 2 = 0⦄`, here evens is a Set and not a type."
  Hint "Sets can only be pulled from a specific Type, you can't have a Set of all natural numbers and -1."
  Hint "In LEAN, the object `0 : ℕ` is different from `0 : ℝ`. If you wanted to have set of (1,π) then the element 1 can't be of type `ℕ` it has to be of the same type as π."
  Hint "Functions are defined from a type to another type not from a Set to another Set."
  exact h

Conclusion "--conc--"
NewTactic rfl
