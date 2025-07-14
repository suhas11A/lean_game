-- import

World "LogicalEquivalence"
Title "Section 1.3: Logical Equivalence"

Introduction "
(Adapted from Page 63 of Infinite Descent)

Consider the following two logical formulae,
where P denotes the set of all prime numbers

(1) ∀n ∈ P, (n > 2 → (∃k ∈ ℤ, n = 2*k+1))
(2) ¬∃n ∈ P, (n > 2 ∧ (∃k ∈ ℤ, n = 2*k))

The logical formula (1) translates to \"every
prime number greater than two is odd \", and
the logical formula (2) translates to \"there does not
exist an even prime number greater than two\".
The statements are _equivalent_—they mean the same thing—but
they suggest different proof strategies:

(1) Fix a prime number n, assume that n > 2, and then prove that n = 2*k+1
for some k ∈ ℤ.
(2) Assume that there is some prime number n such that n > 2 and n = 2*k
for some k ∈ ℤ, and derive a contradiction

While statement (1) more directly translates to plain English, the proof strategy
suggested by (2) is easier to use. This is why we study logical equivalence.
In the first level of this world, we will prove logical formula (2).
"
