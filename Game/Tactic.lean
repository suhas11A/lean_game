-- Custom tactics used by the Infinite Descent game.

import Lean

-- Proceeds with and-introduction.  Works like apply And.intro.
elab "and_intro" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let decl ← goal.getDecl
    let error := Lean.Meta.throwTacticEx `and goal m!"the goal {decl.type} isn't of the form p ∧ q"
    -- Check that the goal type is of the form p ∧ q.
    if let .app (.app and conj1) conj2 := decl.type then
      if (← Lean.Meta.isDefEq and (.const ``And [])) then
        -- Add new metavariables for each conjunct.
        let mvar1 ← Lean.Meta.mkFreshExprMVar conj1
        let mvar2 ← Lean.Meta.mkFreshExprMVar conj2
        -- Close the current goal with And.intro, and add new goals for
        -- each conjunct.
        Lean.Elab.Tactic.closeMainGoal (Lean.mkApp4 (.const ``And.intro []) conj1 conj2 mvar1 mvar2) false
        Lean.Elab.Tactic.setGoals ([Lean.Expr.mvarId! mvar1, Lean.Expr.mvarId! mvar2] ++
                                   (← Lean.Elab.Tactic.getGoals))
      else
        error
    else
      error

example : 0 = 0 ∧ 1 = 1 := by
  and_intro
  · rfl
  · rfl
