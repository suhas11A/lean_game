-- Custom tactics used by the Infinite Descent game.

import Lean
import GameServer.Commands

open Lean.Elab.Tactic Lean.Meta Lean.MonadLCtx

-- Proceeds with and-introduction.  Works like apply And.intro.
elab "and_intro" : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
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
      pure [Lean.Expr.mvarId! mvar1, Lean.Expr.mvarId! mvar2]
    else
      throwTacticEx `and_intro goal
        m!"the goal {decl.type} isn't of the form p ∧ q"

/--
  `and_intro` turns a goal of the form p ∧ q into two goals, p and q.

  This follows Strategy 1.1.7 in Infinite Descent.
 -/
TacticDoc and_intro

example : (0 = 0 ∧ 2 = 2) ∧ 1 = 1 := by
  and_intro
  · and_intro
    · rfl
    · rfl
  · rfl

-- Proceeds with and-elimination.  Replaces a hypothesis of the form
-- p ∧ q with two hypotheses of forms p and q respectively.
elab "and_elim" h:ident "into" hl:ident hr:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    let ctx ← getLCtx
    -- Search for a hypothesis with name h.
    if let some hyp := ctx.findFromUserName? (h.getId) then
      -- If found, ensure that it is of the form p ∧ q
      let whnfHyp ← whnf (← inferType hyp.toExpr)
      if let .app (.app (.const ``And []) conj1) conj2 := whnfHyp then
        -- Use And's eliminators to get values of type p and q and add
        -- them to the context.
        let conj1Val ← mkAppM ``And.left #[hyp.toExpr]
        let conj2Val ← mkAppM ``And.right #[hyp.toExpr]
        let ⟨_, goal, _⟩ ← goal.assertAfter hyp.fvarId hr.getId conj2 conj2Val
        let ⟨_, goal, _⟩ ← goal.assertAfter hyp.fvarId hl.getId conj1 conj1Val
        -- Clear the original hypothesis as it is not needed anymore.
        let goal ← goal.clear hyp.fvarId
        pure [goal]
      else
        throwTacticEx `and_elim goal
          m!"the assumption {h} : {hyp.type} isn't of the form p ∧ q"
    else
      throwTacticEx `and_elim goal
        m!"there is no assumption named {h}"

example (P Q : Prop) (abc : P ∧ Q) : (Q ∧ P) := by
  and_elim abc into a c
  and_intro
  · exact c
  · exact a

/--
  If `h` is the name of an assumption of the form `p ∧ q`, then
  `and_elim h into ha hb` replaces `h` with two assumptions, `ha`
  which proves `p` and `hb` which proves `q`.

  This follows Strategy 1.1.9 in Infinite Descent.
 -/
TacticDoc and_elim
