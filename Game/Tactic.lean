-- Custom tactics used by the Infinite Descent game.

import Lean

open Lean.Elab.Tactic Lean.Meta

-- Proceeds with and-introduction.  Works like apply And.intro.
elab "and_intro" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let decl ← goal.getDecl
    -- Convert the goal to WHNF to compare.
    let whnfGoal ← whnf decl.type
    -- Check that the goal type is of the form p ∧ q.
    if let .app (.app (.const ``And []) conj1) conj2 := whnfGoal then
      -- Add new metavariables for each conjunct.
      let mvar1 ← mkFreshExprMVar conj1
      let mvar2 ← mkFreshExprMVar conj2
      -- Close the current goal with And.intro, and add new goals for
      -- each conjunct.
      goal.assign (← mkAppM ``And.intro #[mvar1, mvar2])
      replaceMainGoal [Lean.Expr.mvarId! mvar1, Lean.Expr.mvarId! mvar2]
    else
      Lean.Meta.throwTacticEx `and_intro goal
        m!"the goal {decl.type} isn't of the form p ∧ q"

example : (0 = 0 ∧ 2 = 2) ∧ 1 = 1 := by
  and_intro
  · and_intro
    · rfl
    · rfl
  · rfl
