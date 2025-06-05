import Game.Metadata
import Mathlib.Tactic.Ring

World "Functions"
Level 1
Title "Extensionality"

Introduction "
Before we go into any theorems, let’s go over how to use function
extensionality in Lean.  This requires the use of a new tactic,
`funext`.

Typing `funext x` will use function extensionality to prove that two
functions are equal.  When you use it, `x` will be introduced as a
natural number and the goal `f = g` will be replaced by `f x = g x`.
You can replace `x` by any other name.  Try typing `funext x` now.
"

/-- The functions $f,g : ℕ → ℕ$ defined by $f(x) = 2x$ and $g(x) = x+x$ are equal. -/
Statement :
  let f : ℕ → ℕ := fun x ↦ 2 * x
  let g : ℕ → ℕ := fun x ↦ x + x
  f = g := by
  funext x
  Hint "
  Great, we applied function extensionality and can proceed with the
  proof.  You can unfold the definition of a function within Lean with
  the dsimp tactic; try `dsimp [f]` and `dsimp [g]` to see what they do.

  Or, you can just complete the proof right now with the `ring` tactic.
  "
  dsimp [f, g]
  Hint "Now, use the `ring` tactic to complete the proof."
  ring

Conclusion ""

NewTactic funext dsimp ring
