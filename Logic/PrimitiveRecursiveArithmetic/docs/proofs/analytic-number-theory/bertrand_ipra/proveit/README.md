# ProveIt client

`BertrandObject.lean` targets the ProveIt checkout at
`1e53ba5b26b144afb01bf6774d75cf35f6c760b2` and its root
`lean-toolchain` (`leanprover/lean4:v4.32.0`). From the root of that
checkout, with its dependencies available, run

```sh
lake build +IPRADerivations.AnalyticNumberTheory.PrimorialLower +IPRADerivations.Foundations.BoundedReflection
lake env lean /absolute/path/to/proveit/BertrandObject.lean
```

The file is a source-level candidate. Its upstream declarations and signatures
were checked against the pinned source. It has not been compiled against that
workspace. The standalone Lean files in the archive have their own build status.

All object derivations use `Γ ⊢[PRAAx] φ`. The first three declarations
establish the single-prime-power bound for the central binomial coefficient,
the exponent bound above its square-root threshold, and vanishing above the
row index. The remainder connects the prime indicator and the repository's
bounded nonzero search to a closed object sentence for the **least** prime in
the interval `n < p < 2n − 2` for `n ≥ 4`. The witness runs through all indices below
`2*n − 2`; the
lower-bound factor in the test excludes every index at most `n`.

The final theorem takes an explicit `failureObligation`. To specialize it
to an unconditional derivation, implement the paper's contradiction from
`found n = 0` and `4 ≤ n`. The instructions below identify its components.

1. Use `Combinatorics.CentralBinomial.central_lower` for the lower bound.
   Use `AnalyticNumberTheory.BinomialLcm.binom_val` and `quo_two` for the
   strip `2n/3 < p ≤ n`. The second and higher quotient terms vanish once
   `p² > 2n`, and the first contributes zero. The declarations
   `prime_power_bound`, `exponent_le_one`, and `exponent_zero_above`
   handle the other valuation bounds.
2. Instantiate `FactorVector.reconstruct` with any object bound exceeding
   both the central coefficient and `2n`, for example their sum plus one.
   Fold the pointwise inequalities into products. The values `2n − 2` and `2n` have proper
   divisor 2. Account for the possible factor `2n − 1` once, using
   `exponent_le_one`. In the open interval use `exclude_interval_prime`.
3. Prove the primorial upper bound using the odd and even cases in the
   paper. `PrimorialLower.prim` supplies the product term.
   A cumulative bounded predicate can encode the induction hypothesis.
   `ChebyshevBounds.upper_step` demonstrates this method in the same
   object calculus for an independent lcm bound.
4. Reify the paper's integer growth lemma and its finite base certificate.
   Fixed numeral facts can be derived with the defining equations. Combine
   the estimates using monotonicity of multiplication and of powers.
5. Pass the resulting open contradiction to `bertrand_of_failure_refuted`.
   It produces the universally quantified object sentence. A first-order
   existential version follows by introducing the witness term using
   `Prf.exI`.

The absolute scan uses `2n − 2` as its sentinel. On the theorem's domain the
least strict-interval prime is independent of the chosen failure convention.
