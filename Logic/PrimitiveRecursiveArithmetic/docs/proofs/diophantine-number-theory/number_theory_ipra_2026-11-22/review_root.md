# Historical review: findings resolved

This review records an intermediate draft. Its foundational circularity finding was corrected before the final report: the Boolean scan is now verified directly by quantifier-free induction before bounded reflection is derived. The zero-input clarification was also incorporated. See `review_additional.md` for the re-review and `verification/final_review.md` for the final disposition. The findings below are retained as an audit trail, not as unresolved objections to the delivered text.

---

# Independent audit of foundations and finite analytic number theory

Reviewed: `chapters/foundations.tex` and `chapters/analytic.tex` as present in the shared workspace when this review was requested. This is a mathematical and proof-theoretic audit, not a Lean compilation or a machine-checked derivability result.

## 1. Required correction: reflection/search proof ordering

The mathematical statements of bounded Boolean reflection and bounded search are correct, but their current proofs contain a circular dependency:

- `fd:reflection` explains bounded existential reflection by appealing to the subsequent scan-correctness lemma.
- `fd:search` verifies its scan invariant by appealing back to the full bounded-reflection lemma.

This should be repaired before claiming that the foundational reductions have been completely justified. It does not require a stronger induction scheme.

### Direct quantifier-free scan proof

For a fixed Boolean primitive recursive function `b(i)` and fixed search bound `T`, define `w_0 = T`, and for `j < T` replace `w_j` by `j` exactly when `w_j = T` and `b(j) = 1`. Otherwise retain it. Define the product of failure bits directly by primitive recursion:

`P_0 = 1`, `P_(j+1) = P_j * (1 - b(j))`.

For `j <= T`, prove the following simultaneous quantifier-free invariants:

1. `w_j <= T` and `P_j = 0 or P_j = 1`.
2. `w_j = T iff P_j = 1`.
3. `w_j < T -> (w_j < j and b(w_j) = 1)`.
4. For a fixed arbitrary parameter `i < T`, `(i < j and b(i) = 1) -> w_j <= i`.

All induction formulas are built from equalities, inequalities and propositional connectives; inequalities have primitive recursive characteristic functions. The bound `T`, parameter `i`, and fixed definition of `b` remain parameters of the induction. The update cases prove the invariants directly: a previously selected success is retained; a first success makes `P` zero and selects `j`; a failed test retains the sentinel and `P = 1`.

At `j = T`, if `P_T = 0`, invariant 2 gives `w_T != T`, invariant 1 gives `w_T < T`, and invariant 3 gives the desired witness. If `P_T = 1`, invariant 4 excludes any successful `i < T`. Universal generalization on the formerly arbitrary fixed `i` gives the failure characterization and leastness.

This argument establishes the Boolean-scan machinery without using bounded reflection. Then:

- use it to complete the bounded existential step of `fd:reflection`;
- present `fd:search` as its already-established corollary;
- or retain the current lemma order but include this direct scan argument in the proof of `fd:reflection`, and have `fd:search` refer to that argument.

The universal product reflection can also be justified directly. For a fixed parameter `i`, quantify-free induction on `j` proves `i < j -> P_j <= b(i)` for the product of success bits. For the converse, retain the fixed hypothesis `forall i < T, b(i)=1` and induct on the quantifier-free formula `j <= T -> P_j=1`. This avoids induction on a universally quantified formula.

## 2. Analytic mathematics: no substantive error found in the reviewed formulas

### Dyadic Chebyshev constants

The lower bound is valid: for `n >= 3`, `2n+1 <= 2^n`; applying this at `n = 2^(K-1)` with `K >= 3` gives the claimed exponent comparison.

The upper bound is also valid. The interval prime products give

`P(2^K) <= 2^(2^(K+1)-2)`.

For `L = ceil(K/2)`, the primes above `2^L` yield the required lower product bound. The auxiliary estimate `L*2^L <= 2^K` holds: for `K=2m`, it reduces to `m <= 2^m`; for `K=2m+1`, to `m+1 <= 2^m`, which is valid already for `m=0`. The final constant 6 therefore follows as written. No logarithm or real-number monotonicity is needed.

### Greedy block-product estimate

The statement and proof are sound. Every nonfinal block has sum greater than `1/4`, every block has sum at most `3/4`, and `prod(1-u_i) >= 1-sum u_i` gives reciprocal product at most 4 per block. The stated `4k+1` block bound is deliberately loose but sufficient. The empty list and the `k=0` case are both covered.

### Explicit prime reciprocal bound

Let `C=4^(4k+1)`, `m=2C`, and `B=2^m`. The harmonic lower bound is exactly `1+C`, whereas the contrary assumption on the prime reciprocal sum gives Euler product at most `C`. Thus the contradiction is correct. The bound is primitive recursive even though enumerating up to it is generally infeasible. Finite checks should test the algebraic construction and block inequalities, rather than imply that the huge prime sum was evaluated.

### Euler-product truncation and error removal

The truncated Euler product consists of distinct reciprocal powers of integers at most `P(N)^J`, so comparison with the finite zeta sum is correct by unique factorization. Each geometric tail is at most `2^(-J)` for `s >= 2`, and the telescoping product estimate is bounded by `N*2^(N-J)` as stated.

The denominator argument removes the error arithmetically. For a positive denominator `D` of the candidate excess, positivity implies excess at least `1/D`. With `J=2N+D+2`,

`N*2^(N-J) <= 2^(-D-2) < 1/D`.

The finite contradiction is valid, including `N=1` when the prime product is empty. No completeness principle or unrestricted real comparison is used.

### Sieve and probabilistic identities

The inclusion-exclusion expansion, prime-counting survivor formula, exact prime-divisor means, CRT independence, and coprime-pair Möbius formula are all correct. Independence is appropriately restricted to a full period given by the product of the distinct primes, rather than asserted for arbitrary initial intervals.

## 3. Minor clarification

In the prime-divisor-mean formulas, write `sum_{1 <= n <= X}` at least once, or explicitly say that `sum_{n <= X}` there ranges over positive integers. The surrounding context clearly intends this, but the base theory uses naturals including zero, and neither `omega(0)` nor `Omega(0)` has been defined.

## 4. Scope and limitations

This review covers the displayed arguments and their proposed reductions to quantifier-free induction. It does not establish that the submitted Lean outline compiles, validate every external repository theorem or schema, or audit other chapters. Finite exact-rational tests in `code/analytic_checks.py` are supplementary implementation checks only.
