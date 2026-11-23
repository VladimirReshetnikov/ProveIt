# Checking the finite Mertens identities

This directory pins Lean 4.19.0. The identical sources also build with Lean 4.32.0, the version used by the ProveIt bridge. Both builds use only their respective standard libraries. From this directory, run

```sh
lean --version
mkdir -p build
lean --root=. -o build/Mertens.olean Mertens.lean
LEAN_PATH=build lean --root=. -o build/PrimeStep.olean PrimeStep.lean
LEAN_PATH=build lean --root=. -o build/Values.olean Values.lean
LEAN_PATH=build lean Audit.lean
```

The verified releases were 4.19.0 (`6caaee842e94`) and 4.32.0 (`8c9756b28d64`). The versioned text files in `verification/` contain all 56 public theorem audits. When checking both versions, select the compiler for each command and use a separate build directory for each version. The names below are in the namespace `Mertens`.

| Mathematical assertion | Checked declaration |
| --- | --- |
| The Möbius inverse satisfies the positive-divisor cancellation law and is uniquely determined by it and its zero convention | `mu_divsum`, `mu_unique` |
| A bounded trial-division factorization multiplies back to its input and has only prime entries | `least_prime_factor`, `factorization` |
| The factor definition and the divisor inverse agree, including the zero case and repeated primes | `mu_prime_step`, `signed_factorization`, `factorMu_correct` |
| The signed interval increment lies between −h and h, and the absolute bound after index 2 improves by 2 | `mu_range`, `M_interval`, `M_bound_after_two` |
| The increments of the Mertens sum are the Möbius values | `M_step` |
| Division counts positive multiples, with and without a weight | `multiple_weight`, `multiple_subsum` |
| The sums over positive lattice points under a hyperbola may be transposed | `summatory_swap`, `weighted_hyperbola` |
| The sum of the Möbius values weighted by floor quotients equals 1 at every positive argument | `weighted_floor_sum` |
| The sum of the Mertens values at the quotient arguments equals 1, with the leading term isolated for computation | `quotient_sum`, `quotient_recurrence` |
| The alternating ordered-tuple formula holds for every cutoff with n < 2^(r+1). The terms vanish when n < 2^r | `hyperboloid`, `no_tuples` |
| Summatory Dirichlet convolution can be evaluated by quotient blocks | `summatory_convolution` |
| The Mertens values weighted by k give the summatory Euler totient, where the totient counts coprime integers | `phi_convolution`, `summatory_totient` |
| All 143 published initial values, with an arbitrary bounded lookup theorem | `computes143`, `lookup143` in `Values.lean` |
| A shared coefficient array evaluates the same summatory function at an arbitrary argument | `fastM_correct` |

`sum f n` visits the indices 1 through n. The array `table n` stores the solutions to the triangular divisor equations at indices 0 through n. The value at index 0 is a convention, and every divisor sum excludes it. The definition `tupleCount r n` counts ordered r-tuples recursively by the first coordinate. Its empty tuple contributes once when n ≥ 1. All functions used to calculate numbers are executable.

## Replaying the conventional definition

The module `PrimeStep.lean` proves the identification directly. Split the divisor sum of p*n into divisors divisible by the prime p and divisors coprime to p. The first part is indexed by the divisors of n, and the second runs through divisors of n coprime to p. Uniqueness for the zero divisor sum gives μ(pn)=0 if p divides n and μ(pn)=−μ(n) otherwise. Bounded search finds the least divisor greater than 1, and `least_prime_factor` proves it prime. Repeated division produces an explicit list in `primeList n n`. The proof checks the product, primality of all entries, and the equivalence between prime membership and divisibility. Testing the list for repeated entries and taking the parity sign of its length therefore yields `factorMu_correct`. The paper also gives the direct subset pairing proof of divisor cancellation.

## Scope of the kernel check and the object theory

The files check ordinary Lean propositions over `Nat`, `Int`, and primitive-recursive bounded sums. `Audit.lean` reports the Lean axioms for the individual theorems. The universal floor, totient, and ordered-tuple identities use `propext` and `Quot.sound`. The proofs of the quotient update rules use the two elementary inequalities that characterize Euclidean division. No proof in the files uses a placeholder or a user axiom.

An iPRA proof object requires a separate reification. Encode signed integers as natural codes with 0 for zero, 2a−1 for +a, and 2a for −a (a ≥ 1). Use primitive-recursive list codes for arrays, with append and indexed lookup, and specialize every function-parameter sum to the named functions in its application. Express the invariant for `table_stable` as a bounded conjunction of equalities for indices at most the current size. For `mu_unique`, use the invariant that all positive indices up to the induction index have equal coefficients. For the changing argument in `no_tuples` and `hyperboloid`, fix the original bound N and conjoin the implication for all n ≤ N. A recursive call uses n/(k+1) ≤ n. Compile the bounded conjunctions and divisibility conditions into primitive-recursive zero-one tests. Integer equality and comparison reduce to equality and comparison of their codes. Every induction for these specialized statements then has a quantifier-free invariant.

For a ProveIt integration, define the corresponding primitive-recursion program codes, prove their equations in Foundation's `IPRAStandardTheory.standardTheory`, and assemble the bounded inductions just described. The existing `IPRABridge.standardToConcise` accepts a closed object derivation in that theory and returns a derivation of its translated sentence in ConciseIPRA. The bridge expects the object derivation as input. The files in this directory supply semantic Lean proofs and implementation definitions. The repository's toolchain for the bridge is recorded independently from the standalone checker here. [ProveIt bridge](https://github.com/VladimirReshetnikov/ProveIt/tree/main/Logic/PrimitiveRecursiveArithmetic/Bridge) · [ProveIt endpoints](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Logic/PrimitiveRecursiveArithmetic/ENDPOINTS.md)
