**June 25**
potential exercise: (p \imp r) \and (q \imp r) \imp (p \or q \imp r)
outermost operator is \imp becuase it has highest precedence, not \and because it is the first that appears outside of parentheses
proof strategy for p \imp q, assume p and derive q
formulas that are true no matter what values p, q, r take are called tautologies
inverse versus contrapositive, converse of the inverse is the contrapositive
proof by contradiction explained with negation operator
spent time on law of excluded middle and principle of explosion
making an assumption is not same as stating that something is necessarily true. for sqrt(2) ^ sqrt(2) example, we don't have to state if it is rational or irrational, suffices to prove goal in both cases
- maybe it would help to state in general terms:
((p \imp r) \and (\neg p \imp r)) \imp r
- nonconstructive proof, andreij bauer

**June 26**
- _little_ more explanation that p(a) = p(b) -> a = b is same as uniqueness (there is only one x \in X satisfying p(x))
- free versus bound variables
- density of rationals

**June 27**
- commas are ambiguous, should specify "for some" or "there exists __ such that"
- p \or q logically equivalent to \neg p \imp q, suggests proof strategy of assuming p is not true and deducing that q is true, otherwise, p is true. in both cases, p or q is true
- maximally negated: negation only appears in front of predicates (we can push negation inside logical operators and quantifiers)
- \neg in front of the first quantifier actually means parentheses around entire thing, not just the first quantifer
- \neg (p \imp q) congruent to p \and \neg q
- don't need density of reals for that exercise, should add it back (just take average of the two numbers and prove that it is greater than x
and less than y)

**June 30**
- definition of universe
- \forall x \in X, p(x) is equivalent to \forall x, (x \in X \imp p(x)) (we can just omit specifying the universe)
- what is the unviersal set versus the universe of discourse?
- E is empty set, prove \forall x \in E, p(x) is always true. proof: take x to be arbitrary element of E, but E is empty, so this is a contradiction. By principle of explosion, false implies anything so p(x) is true.
- define A \subset B as \forall x \in A, x\ in B. (so we should unfold this defn in Set world)
- prove if X \subset Y, then P(X) \subset P(Y)
Take arbitrary A \in P(X) (want A \in P(Y))
A is subset of X, so A subset of Y
So any elt of A is in Y
So A \in P(Y)
- (0,1) example: using the principle of explosion is more formal but might make sense to just say that the second case is impossible so only the first case can happen
- proving if E and E' are empty sets then they are equal: instead of principle of explosion can use one of the previous examples where p(x) is x \in E'

actionable items:
- unfold subset defn in set world

**July 7**


