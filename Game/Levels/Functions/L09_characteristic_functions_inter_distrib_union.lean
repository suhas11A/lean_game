import Game.Metadata
import Game.Levels.Functions.L05_characteristic_functions
import Game.Levels.Functions.L06_characteristic_functions_inter
import Game.Levels.Functions.L07_characteristic_functions_union
import Game.Levels.Functions.L08_characteristic_functions_compl
import Mathlib.Tactic.Ring

World "Functions"
Level 9
Title "Characteristic functions: Intersection distributes over union"

Introduction "
We now follow Example 3.1.29, proving that set intersection
distributes over set union, using characteristic functions.

As in the textbook, we will be using the previous four theorems in
order to rewrite set identities in terms of characteristic function
identities.  The names of the theorems are
`characteristic_function_equality`, `characteristic_function_inter`,
`characteristic_function_union`, and `characteristic_functions_compl`.

We will also provide a new theorem, free of charge, that says that a
value of a characteristic function is equal to its square.  This
theorem is named `characteristic_function_square`.

Begin by rewriting with Theorem 3.1.25, `characteristic_function_equality`.
"

open Set

theorem characteristic_function_square (X : Type) (U : Set X) (a : X) : (χ U a) ^ 2 = χ U a := by
  have h := characteristic_function_value U a
  cases h <;> rw [h_1] <;> simp

/-- Let $X$, $Y$, and $Z$ be sets.  Then $X∩(Y∪Z) = (X∩Y)∪(X∩Z)$.
 -/
Statement (U : Type) (X Y Z : Set U) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  rw [characteristic_function_equality]
  Hint "
  Our theorems are framed in terms of the values of characteristic
  functions, so we need to prove these functions are equal with
  function extensionality.  Use `funext` to do so.
  "
  funext
  Hint "
  Now, the left-hand side is the characteristic function of a set
  intersection, so rewrite using `characteristic_function_inter`.
  "
  rw [characteristic_function_inter]
  Hint "
  We have the characteristic function of a set union on the left-hand
  side, so rewrite using `characteristic_function_union`.
  "
  rw [characteristic_function_union]
  Hint "
  We have the characteristic function of a set union on the right-hand
  side, so rewrite using `characteristic_function_union`.
  "
  rw [characteristic_function_union]
  Hint "
  Finally, we have lots of characteristic functions of set
  intersections on the right-hand side, so repeatedly rewrite using
  `characteristic_function_inter`.
  "
  repeat rw [characteristic_function_inter]
  Hint "
  Now our goal has been entirely rewritten in terms of characteristic
  functions of ${X}$, ${Y}$, and ${Z}$.  We will need to rearrange
  some terms on the right-hand side to simplify, but we can let Lean
  do that for us with the `ring_nf` tactic.  Use that now.
  "
  ring_nf
  Hint "
  We can get rid of the square on the right-hand side by using
  `characteristic_function_square`.
  "
  rw [characteristic_function_square]
  Hint "
  Both sides are equal up to simple arithmetic, so we can use `ring`
  to close off the proof.
  "
  ring

Conclusion "

"

NewTheorem characteristic_function_inter characteristic_function_union characteristic_function_compl characteristic_function_square
NewTactic ring_nf «repeat»
