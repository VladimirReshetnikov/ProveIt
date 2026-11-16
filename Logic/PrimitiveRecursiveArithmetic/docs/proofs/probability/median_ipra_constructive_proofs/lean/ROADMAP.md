# Lean formalization roadmap

## Status boundary

`MedianFiniteBlueprint.lean` is an ambient Lean specification. It contains no
`sorry` and introduces no theorem axiom, but its proof-package records are not
constructed. `MedianObjectLanguageTarget.lean` states the actual endpoint: a
closed `Fm PTm 0` accompanied by a `Prf PRAAx` derivation. Standard-model
truth, a theorem about `List`, or a Mathlib theorem about `Real` is not that
endpoint.

## Phase 1 - sequence and rational encodings

Reuse `Core/Pairing` for a natural-number sequence code. Store a length and a
bounded projection; malformed inputs receive a total default. Signed integers
are differences as in `Core/Integers`. A rational is `(sign numerator,
positive denominator)`; comparisons and equality are cross-multiplied, so the
main finite theory uses only natural-number identities and order.

Prove, in `Prf PRAAx`, projection equations and bounded extensionality for
valid sequences. The existing PA `ListCoding` development is a semantic and
engineering reference, especially its division-free `TwiceMedian` relation,
but it is not itself an iPRA derivation.

## Phase 2 - counting and sorting

Define Boolean `<`, `=`, and `<=` tests using `Core/Order`; define
`ltCount(v,t)` and `gtCount(v,t)` by a bounded sum. Implement insertion sort by
primitive recursion. Its invariant is a pair of finite certificates:

1. the output is nondecreasing;
2. a coded index list witnesses that it is a permutation.

Use `Core/Permutation` for reindexing consequences. Prove that the two middle
indices are in range on nonempty input and define lower and upper middle
values.

## Phase 3 - equivalence of median definitions

The central object-language theorem is

```text
2*ltCount(v,t) <= len(v) and 2*gtCount(v,t) <= len(v)
iff
lowerMiddle(v) <= t <= upperMiddle(v).
```

The forward direction counts entries before and after the middle indices. The
reverse direction uses sortedness. Odd/even formulas and uniqueness of twice
the conventional median are immediate. This theorem also gives order-only
invariance and the quartile/decile/percentile identifications.

## Phase 4 - absolute deviations and robustness

Pair the `i`th and `(n-1-i)`th sorted observations. For a point in the middle
interval each pair contributes exactly the endpoint difference; outside the
interval one pair contributes strictly more. Formalize the same argument for
weights by proving the finite-difference identity

```text
D(t+1)-D(t) = 2*massLE(t)-totalMass
```

on integer-scaled data.

For the mean-median inequality prove directly, after clearing denominators,

```text
(2*S-M*W)^2 <= 4*(W*Q-S^2),
```

where `M` is twice a median. A convenient route is the algebraic
Cauchy-Schwarz identity

```text
W*sum(w_i*d_i^2) - (sum(w_i*d_i))^2
 = sum_{i<j} w_i*w_j*(d_i-d_j)^2.
```

Rank robustness is proved by deleting the at most `r` changed coordinates and
counting unchanged observations on each side. The replacement breakdown point
then follows as `ceil(n/2)/n`.

## Phase 5 - finite probability

Represent a law by increasing support values and natural weights with positive
total `W`. Every probability statement is an integer numerator inequality over
`W`; no real numbers are needed. Prove the CDF characterization, existence,
nonuniqueness interval, symmetry results, and exact odd-sample formulas:

```text
P(M_N = v_j) * W^N
 = sum_{i<=n,k<=n} N!/(i!k!(N-i-k)!) A^i C^k B^(N-i-k),
```

where `N=2n+1`, `A` is weight below `v_j`, `B` weight at it, and `C` weight
above it. The CDF is the corresponding binomial tail. `Core/MultiSums`,
`Combinatorics/Binomial`, and factorial equations provide the needed library.

## Phase 6 - algorithms and applications

Formalize compare-swap networks, median-of-three, and the nine-input ninther.
The ninther proof is a four-on-each-side counting argument. For deterministic
linear selection, use groups of five and a recursion trace; prove a
primitive-recursive linear cost majorant by quantifier-free induction.

Theil-Sen, Walsh averages, median filters, conditional finite laws, and
one-dimensional k-medians reduce to constructing a finite derived list and
applying the core median and L1 theorems.

## Phase 7 - effective analysis

Continuous laws, logarithms, square roots, geometric medians, and asymptotic
sample-median normality must use regular rational interval names with explicit
primitive-recursive moduli. Reuse the finite-law and regular-name architecture
of the constructive CLT packet. Derive the exact binomial law first; then apply
an effective binomial CLT and an explicit local inverse-CDF modulus. Do not
replace this step by an ambient theorem about `Real`.

## Phase 8 - integration and audit

Add completed modules under
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/`, import
them from `IPRADerivations.lean`, run `lake build IPRADerivations`, and extend
`Checks/Axioms.lean`. Every public theorem should have type

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] phi
```

and then be transferred with `pra_iff_native`.
