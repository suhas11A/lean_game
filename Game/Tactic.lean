-- Custom tactics used by the Infinite Descent game.

import Lean
import GameServer.Commands

open Lean Elab.Tactic Meta MonadLCtx


-- Helper functions from later versions of the Lean standard library.
namespace List
def flatten : List (List α) → List α
  | []      => []
  | l :: L => l ++ flatten L
@[inline]
def flatMapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
    (f : α → m (List β)) (as_ : List α) : m (List β) :=
  let rec loop
    | [],     bs => pure bs.reverse.flatten
    | a :: as_, bs => do
      let bs' ← f a
      loop as_ (bs' :: bs)
  loop as_ []
@[inline] protected def singleton {α : Type u} (a : α) : List α := [a]
end List

partial def and_intro.go (goal : MVarId) : MetaM (List MVarId) := do
  -- Convert the goal to WHNF to compare.
  let decl ← goal.getDecl
  let whnfGoal ← whnf decl.type
  -- Check that the goal type is of the form p ∧ q.
  if let .app (.app (.const ``And []) conj1) conj2 := whnfGoal then
    -- Add new metavariables for each conjunct.
    let mvar1 ← mkFreshExprMVar conj1
    let mvar2 ← mkFreshExprMVar conj2
    -- Close the current goal with And.intro, and add new goals for
    -- each conjunct.
    goal.assign (← mkAppM ``And.intro #[mvar1, mvar2])
    List.flatMapM go [Expr.mvarId! mvar1, Expr.mvarId! mvar2]
  else
    pure [goal]

-- Proceeds with and-introduction.  Works like apply And.intro.
elab "and_intro" : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    -- Convert the goal to WHNF to compare.
    let decl ← goal.getDecl
    let whnfGoal ← whnf decl.type
    -- Check that the goal type is of the form p ∧ q.
    if let .app (.app (.const ``And []) _) _ := whnfGoal then
      and_intro.go goal
    else
      throwTacticEx `and_intro goal
        m!"the goal {decl.type} isn't a conjunction"

/--
  If the goal is a conjunction, `and_intro` will replace the goal with
  each of its conjuncts, in turn.

  This follows Strategy 1.1.7 in Infinite Descent.
 -/
TacticDoc and_intro

example : (0 = 0 ∧ 2 = 2) ∧ 1 = 1 := by
  and_intro
  · rfl
  · rfl
  · rfl


partial def and_elim.go (hyp : FVarId) (goal : MVarId) (type value : Expr) (conjs : List Name) :
    MetaM (MVarId × List Name) := do
  if let .app (.app (.const ``And []) conj1) conj2 := (← whnf type) then
    let ⟨goal, conjs⟩ ← go hyp goal conj2 (← mkAppM ``And.right #[value]) conjs
    go hyp goal conj1 (← mkAppM ``And.left #[value]) conjs
  else
    match conjs with
    | [] => throwTacticEx `and_elim goal m!"not enough conjunct names provided"
    | conj :: conjs =>
      let ⟨_, goal, _⟩ ← goal.assertAfter hyp conj type value
      pure ⟨goal, conjs⟩

-- Proceeds with and-elimination.  Replaces a conjunction hypothesis
-- with separate hypotheses for each conjunct.
elab "and_elim" h:ident "into" conjs:ident,+ : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    let ctx ← getLCtx
    -- Search for a hypothesis with name h.
    if let some hyp := ctx.findFromUserName? (h.getId) then
      let hypType ← inferType hyp.toExpr
      -- If found, ensure that it is of the form p ∧ q
      if let .app (.app (.const ``And []) _) _ := (← whnf hypType) then
        let conjs := List.reverse $ TSyntax.getId <$> conjs.getElems.toList
        let ⟨goal, remaining_conjs⟩ ← and_elim.go hyp.fvarId goal hypType hyp.toExpr conjs
        if let _::_ := remaining_conjs then
          throwTacticEx `and_elim goal m!"too many conjunct names provided"
        -- Clear the original hypothesis as it is not needed anymore.
        let goal ← goal.clear hyp.fvarId
        pure [goal]
      else
        throwTacticEx `and_elim goal
          m!"the assumption {h} : {hyp.type} isn't a conjunction"
    else
      throwTacticEx `and_elim goal
        m!"there is no assumption named {h}"

example (P Q : Prop) (abc : P ∧ Q ∧ R) : (Q ∧ R ∧ P) := by
  and_elim abc into a, b, c
  and_intro
  · exact b
  · exact c
  · exact a

/--
  todo i have to update this, don't wanna rn lol
  If `h` is the name of an assumption of the form `p ∧ q`, then
  `and_elim h into ha hb` replaces `h` with two assumptions, `ha`
  which proves `p` and `hb` which proves `q`.

  This follows Strategy 1.1.9 in Infinite Descent.
 -/
TacticDoc and_elim


/--
  If expr is a possibly nested disjunction, and disj is one of the
  disjuncts, then extractDisjunct expr disj returns ok e, where e is a
  composition of Or.inl or Or.inr that can be used to construct a term
  of type expr using a term of type disj.
  -/
partial def extractDisjunct (expr disj : Expr) : MetaM (Except MessageData Expr) := do
  if ← isDefEq expr disj then
    pure $ .ok $ .app (.const ``id [.zero]) expr
  else if let .app (.app (.const ``Or []) disj1) disj2 := (← whnf expr) then
    if let .ok inDisj1 := (← extractDisjunct disj1 disj) then
      .ok <$> mkAppM ``Function.comp #[mkApp2 (.const ``Or.inl []) disj1 disj2, inDisj1]
    else if let .ok inDisj2 := (← extractDisjunct disj2 disj) then
      .ok <$> mkAppM ``Function.comp #[mkApp2 (.const ``Or.inr []) disj1 disj2, inDisj2]
    else
      pure $ .error m!"{disj} is not one of the disjuncts of {expr}"
  else
    pure $ .error m!"{expr} is not a disjunction"

-- Proceeds with or-introduction.  If the goal is a disjunction, then
-- the user specifies which disjunct to prove by writing the proposition
-- out instead of picking the left or right branch.
elab "or_intro" disj:term : tactic =>
  withMainContext do
    let disj ← elabTerm disj (expectedType? := some $ .sort .zero)
    liftMetaTactic λ goal ↦ do
      match ← extractDisjunct (← goal.getType) disj with
      | .ok k =>
        let mvar ← mkFreshExprMVar disj
        goal.assign (.app k mvar)
        pure [Expr.mvarId! mvar]
      | .error m =>
        throwTacticEx `and_intro goal m

example (x y z : Nat) : x = y ∨ y = y ∨ y = z := by
  or_intro y = y
  rfl

/--
  If the goal is a disjunction, and `disj` one of its disjuncts, then
  `or_intro disj` will replace the goal with `disj` for you to prove.

  For instance, if the goal is `x = y ∨ y = y ∨ y = z`, then `or_intro
  y = y` will replace the goal with `y = y`.

  This follows Strategy 1.1.13, proving disjunctions, in Infinite Descent.
  -/
TacticDoc or_intro


partial def or_elim.go (hyp : FVarId) (goal : MVarId) :
    StateT (List Name) MetaM (List MVarId) := do
  goal.withContext do
    if let .app (.app (.const ``Or []) disj1) disj2 ← whnf (← hyp.getType) then
      -- The hypothesis is a disjunction; eliminate it.
      let goalType ← goal.getType
      let ⟨cases_, newGoals⟩ ← List.unzip <$> [disj1, disj2].mapM λ disj ↦ do
        -- Create a metavariable for the argument to Or.elim.  Clear the
        -- old hypothesis; it is not needed anymore.
        let case ← ((mkArrow disj goalType >>= mkFreshExprMVar ∘ some) <&>
                     Lean.Expr.mvarId! >>= Lean.MVarId.clear (fvarId := hyp)
                     : MetaM _)
        -- Introduce the disjunct and recurse.
        let ⟨subHyp, subGoal⟩ ← case.intro1
        let subGoals ← go subHyp subGoal
        pure (Expr.mvar case, subGoals)
      goal.assign =<< mkAppM ``Or.elim (Expr.fvar hyp :: cases_).toArray
      pure newGoals.flatten
    else
      -- The hypothesis is not a disjunction; name the disjunct.
      match ← get with
      | [] => throwTacticEx `or_elim goal m!"not enough disjunct names provided"
      | name :: names => set names ; .singleton <$> goal.rename hyp name

-- Proceeds with or-elimination.  Eliminates a (possibly recursive)
-- disjunction hypothesis and adds a goal for each disjunct.
elab "or_elim" h:ident "into" disjs:ident,+ : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    let ctx ← getLCtx
    -- Search for a hypothesis with name h.
    if let some hyp := ctx.findFromUserName? (h.getId) then
      let hypType ← inferType hyp.toExpr
      -- If found, ensure that it is a disjunction
      if let .app (.app (.const ``Or []) _) _ := (← whnf hypType) then
        let disjs := TSyntax.getId <$> disjs.getElems.toList
        let ⟨goals, remaining_disjs⟩ ← or_elim.go hyp.fvarId goal disjs
        if let _::_ := remaining_disjs then
          throwTacticEx `or_elim goal m!"too many disjunct names provided"
        pure goals
      else
        throwTacticEx `or_elim goal
          m!"the assumption {h} : {hyp.type} isn't a disjunction"
    else
      throwTacticEx `or_elim goal
        m!"there is no assumption named {h}"

example (h : 1 = 1 ∨ 1 = 1 ∨ 1 = 1) : 1 = 1 := by
  or_elim h into a, b, c
  · exact a
  · exact b
  · exact c

/-- If `h` is a disjunction assumption with `n` disjuncts, then
    `or_elim h into h1, h2, h3, ..., hn` will add a goal where each
    one of the disjuncts is true in turn, and will name the ith
    disjunct `hi`.  You may pass whatever names for the disjuncts that
    you wish, but you need to provide as many names as there are
    disjuncts.
  -/
TacticDoc or_elim


-- Implies-introduction.  Works like intro, but checks that the variable
-- being introduced is a proposition.
elab "imp_intro" h:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal => do
    let goalType ← goal.getType
    if let .forallE _ hypType _ _ ← whnf goalType then
      if ← Expr.isProp <$> inferType hypType then
        let ⟨_, goal⟩ ← goal.intro h.getId
        pure [goal]
      else
        throwTacticEx `imp_intro goal m!"{hypType} is not a proposition"
    else
      throwTacticEx `imp_intro goal m!"{goalType} is not an implication"

example (x : Nat) : x = 1 → x = 1 := by
  imp_intro h
  exact h


-- Implies-elimination, applying one hypothesis with another.
elab "imp_elim" imp:ident "with" hyp:ident "into" conc:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal => do
    if let some imp := (← getLCtx).findFromUserName? (imp.getId) then
      if let some hyp := (← getLCtx).findFromUserName? (hyp.getId) then
        if let .forallE _ hypType concType _ ← whnf imp.type then
          if ← isDefEq hypType hyp.type then
            let ⟨_, goal⟩ ← goal.assert conc.getId concType (.app (.fvar imp.fvarId) (.fvar hyp.fvarId))
                             >>= MVarId.intro1P
            pure [goal]
          else
            throwTacticEx `imp_elim goal m!"the hypothesis of {imp.type} is not {hyp.type}"
        else
          throwTacticEx `imp_elim goal m!"{imp.type} is not an implication"
      else
        throwTacticEx `imp_elim goal m!"assumption {hyp} not found"
    else
      throwTacticEx `imp_elim goal m!"assumption {imp} not found"

example (x y : Nat) : (x = 1 → y = 2) → x = 1 → y = 2 := by
  imp_intro imp
  imp_intro x1
  imp_elim imp with x1 into conc
  exact conc

-- Implies-elimination, applying a hypothesis to the goal.
elab "imp_elim" imp:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal => do
    if let some imp := (← getLCtx).findFromUserName? (imp.getId) then
      if let .forallE _ _ goalType _ ← whnf imp.type then
        if ← isDefEq goalType (← goal.getType) then
          goal.apply (.fvar imp.fvarId)
        else
          throwTacticEx `imp_elim goal m!"the conclusion of {imp.type} is not {← goal.getType}"
      else
        throwTacticEx `imp_elim goal m!"{imp.type} is not an implication"
    else
      throwTacticEx `imp_elim goal m!"assumption {imp} not found"

example (x y : Nat) : (x = 1 → y = 2) → x = 1 → y = 2 := by
  imp_intro imp
  imp_intro x1
  imp_elim imp
  exact x1


-- Biconditional introduction; turns a goal of the form p ↔ q into a
-- goal p → q and a goal q → p.
elab "iff_intro" : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    -- Convert the goal to WHNF to compare.
    let decl ← goal.getDecl
    let whnfGoal ← whnf decl.type
    -- Check that the goal type is of the form p ↔ q.
    if let .app (.app (.const ``Iff []) p) q := whnfGoal then
      -- Add new metavariables for each conditional.
      let mvar1 ← mkFreshExprMVar =<< mkArrow p q
      let mvar2 ← mkFreshExprMVar =<< mkArrow q p
      -- Close the current goal with Iffn.intro, and add new goals for
      -- each conditional.
      goal.assign (← mkAppM ``Iff.intro #[mvar1, mvar2])
      pure [Expr.mvarId! mvar1, Expr.mvarId! mvar2]
    else
      throwTacticEx `iff_intro goal
        m!"the goal {decl.type} isn't a biconditional"

example : 1 = 1 ↔ 2 = 2 := by
  iff_intro
  · imp_intro h
    rfl
  · imp_intro h
    rfl


-- Biconditional elimination; turns a hypothesis of the form p ↔ q into
-- a hypothesis p → q and a hypothesis q → p.
elab "iff_elim" iff:ident "into" fw:ident "," bw:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal ↦ do
    if let some iff := (← getLCtx).findFromUserName? (iff.getId) then
      if let .app (.app (.const ``Iff []) p) q ← whnf iff.type then
        let ⟨_, goal, _⟩ ← goal.assertAfter iff.fvarId bw.getId (← mkArrow q p)
                            =<< mkAppM ``Iff.mpr #[.fvar iff.fvarId]
        let ⟨_, goal, _⟩ ← goal.assertAfter iff.fvarId fw.getId (← mkArrow p q)
                            =<< mkAppM ``Iff.mp #[.fvar iff.fvarId]
        List.singleton <$> goal.clear iff.fvarId
      else
        throwTacticEx `iff_elim goal m!"{iff.type} is not a biconditional"
    else
      throwTacticEx `iff_elim goal m!"assumption {iff} not found"

example (p q : Prop) : (P ↔ Q) → (P → Q) ∧ (Q → P) := by
  imp_intro h
  iff_elim h into h1, h2
  and_intro
  · exact h1
  · exact h2


-- Universal quantification introduction
elab "forall_intro" var:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal => do
    let goalType ← goal.getType
    if let .forallE _ hypType _ _ ← whnf goalType then
      if ← not <$> Expr.isProp <$> inferType hypType then
        let ⟨_, goal⟩ ← goal.intro var.getId
        return [goal]
    throwTacticEx `imp_intro goal m!"{goalType} is not universally quantified"

example : ∀ (x : Nat), x = x := by
  forall_intro y
  rfl


-- Universal quantification elimination
elab "forall_elim" hyp:ident "of" obj:term "into" conc:ident : tactic =>
  withMainContext do
    let obj ← elabTerm obj none
    liftMetaTactic λ goal => do
      if let some hyp := (← getLCtx).findFromUserName? (hyp.getId) then
        let objType ← inferType obj
        if let .forallE _ hypObjType _ _ ← whnf hyp.type then
          if ← not <$> Expr.isProp <$> inferType hypObjType then
            if ← isDefEq hypObjType objType then
              let hypVal ← mkAppM' (.fvar hyp.fvarId) #[obj]
              let ⟨_, goal⟩ ← goal.assert conc.getId (← inferType hypVal) hypVal
                               >>= MVarId.intro1P
              return [goal]
            else
              throwTacticEx `forall_elim goal m!"{hypObjType} is not quantified over {objType}"
        throwTacticEx `forall_elim goal m!"{hyp.type} is not universally quantified"
      else
        throwTacticEx `forall_elim goal m!"assumption {hyp} not found"

example (h : ∀ (x : Nat), x = x) : 2 = 2 := by
  forall_elim h of 2 into h1
  exact h1

example (h : ∀ (x : Nat), x = x) (y : Nat) : y + 1 = y + 1 := by
  forall_elim h of y + 1 into h1
  exact h1


-- Existential quantification introduction
elab "exists_intro" obj:term : tactic =>
  withMainContext do
    let obj ← elabTerm obj none
    liftMetaTactic λ goal => do
      if let .app (.app (.const ``Exists _) α) p ← whnf =<< goal.getType then
        if ← isDefEq α =<< inferType obj then
          goal.apply =<< mkAppOptM ``Exists.intro #[none, p, obj]
        else
          throwTacticEx `exists_intro goal m!"{← goal.getType} is not quantified over {← inferType obj}"
      else
        throwTacticEx `exists_intro goal m!"{← goal.getType} is not existentially quantified"

example : ∃ (x : Nat), 2 * x = 4 := by
  exists_intro 2
  trivial


-- Existential quantification elimination
elab "exists_elim" hyp:ident "into" var:ident "," conc:ident : tactic =>
  withMainContext $ liftMetaTactic λ goal => do
    if let some hyp := (← getLCtx).findFromUserName? (hyp.getId) then
      if let .app (.app (.const ``Exists _) _) _ ← whnf hyp.type then
        if let [goal] ← goal.apply =<< mkAppOptM ``Exists.elim #[none, none, ← inferType (.mvar goal),
                                                                  some (.fvar hyp.fvarId)] then
          let ⟨_, goal⟩ ← goal.introN 2 [var.getId, conc.getId]
          pure [goal]
        else
          throwTacticEx `forall_elim goal m!"this should not happen"
      else
        throwTacticEx `forall_elim goal m!"{hyp.type} is not existentially quantified"
    else
      throwTacticEx `forall_elim goal m!"assumption {hyp} not found"

example (h : ∃ (x : Nat), 2 * x = 4) : ∃ (x : Nat), ∃ (y : Nat), x * y = 4 := by
  exists_elim h into x, h
  exists_intro 2
  exists_intro x
  exact h
