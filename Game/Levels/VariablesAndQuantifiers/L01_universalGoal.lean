import Game.Metadata
import GameServer.Commands

World "VariablesAndQuantifiers"
Level 1
Title "Universal Quantifier in the Goal"

-- ch.0: arithmetic, exponents, inequalities

Introduction "Definition 1.2.9 states that if p(x) is a logical formula
with free variable x with range X, then \\"\forall x \in X, p(x)\\" is
the logical formula defined according to two rules. The introduction
rule is \\"If p(x) can be derived from the assumption that x is an
arbitrary element of X, then \forall x \in X, p(x),\\" which we will invoke
using the
`forall_intro` tactic."
Statement
NewTactic
Conclusion
