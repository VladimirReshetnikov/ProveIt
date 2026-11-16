# Lean and object-language formalization roadmap

## 1. Target

For each theorem family, the final artifact should contain an explicit
`PRAAx` derivation

```lean
([] : List (Fm PTm k)) ⊢[PRAAx] theoremOpen
```

followed by universal closure and, when desired, transport through

```lean
pra_iff_native
```

from `ConciseIPRA.NativeBiInterpretation`.

The finite theorem family is the first milestone.  No arbitrary `Real`, measure,
or infinite set is needed there.

## 2. Reusable ProveIt modules

The inspected repository baseline is commit
`df3ff8cc28be5eb713a14809a9df167e9aa94ab1`.

Use these checked modules first:

- `IPRADerivations.Core.BoundedSums`
  - `sum_zero_elim`, `sum_zero_of_all`, `sum_zero_of_bounded`;
- `IPRADerivations.Core.SumLemmas`
  - `sum_shift`, `sum_add`, `sum_congr_bounded`, `term_le_sum`;
- `IPRADerivations.Core.MultiSums`
  - finite Fubini/reindexing for product spaces;
- `IPRADerivations.Core.Pairing`
  - coding outcomes and product indices;
- the arithmetic/order/ring modules underlying `deriveNat`, `le`, `lt`,
  truncated subtraction, division with remainder, and simultaneous recursion;
- `ConciseIPRA.NativeBiInterpretation`
  - the `pra_iff_native` bridge.

The probability CLT packet already uses the useful ambient structures
`FinLaw`, `Regular`, and the `InternalProof` endpoint pattern.  This packet's
files deliberately align with those names.

## 3. Milestone A: ambient finite semantics

File: `lean/ExpectedValueFinite.lean`.

1. Define `FinLaw` with natural weights and a positive total.
2. Define rational expectation, event probability, mean, second moment,
   variance, positive/negative parts, and CDF.
3. Prove in ambient Lean:
   - normalization and constants;
   - additivity/homogeneity/finite linearity;
   - nonnegativity, monotonicity, convex-hull bounds;
   - almost-sure equality and nondegeneracy;
   - indicator expectation and finite LOTUS;
   - finite tail-sum and signed CDF formulas;
   - variance identity;
   - Markov, Chebyshev, Cauchy--Schwarz;
   - product-law multiplicativity;
   - finite conditional expectation and total expectation;
   - sample-mean formulas and the squared-residual identity.
4. Keep proofs denominator-cleared whenever possible so the object-language
   translation is visible rather than hidden inside field automation.

## 4. Milestone B: natural-number encodings

Introduce:

```lean
structure ZCode where pos neg : Nat
structure QCode where num : ZCode; den : Nat; denPos : 0 < den
structure FinLawCode where
  card total commonDen : Nat
  weight : Nat -> Nat
  valueNum : Nat -> ZCode
```

All arrays are represented by one natural using the existing pairing/list
coding.  Normalize a finite rational list to one positive common denominator.
Define primitive-recursive functions:

```text
weightSum, weightedNum, eventMass, absWeightedNum,
secondMomentNum, tailMass, fiberMass, productIndex,
firstCrossingMass, finiteMoment
```

Invalid codes return a benign value and the open theorem is written as an
implication encoded by the standard zero-test convention.

## 5. Milestone C: object-language finite kernel

File: `lean/ObjectLanguageTargets.lean`.

Prove the defining equations of all functions above.  Then derive:

1. `expect_add_open` by `sum_add` and the ring tool;
2. `expect_mono_open` by pointwise nonnegative differences;
3. `indicator_open` by unfolding the event mass;
4. `lotus_open` by a bounded double sum and `MultiSums`;
5. `tail_sum_open` by QF induction on the integer value and finite Fubini;
6. `variance_open` by polynomial normalization;
7. `markov_open` by a pointwise inequality and summation;
8. `chebyshev_open` as an instance of Markov;
9. `cauchy_schwarz_open` from the finite Lagrange identity;
10. `independent_product_open` by distributivity of the product sum;
11. `sample_mean_open` by QF induction on the sample count;
12. `kolmogorov_open` by first-crossing event coding.

Each is then universally closed.  Aggregate them into one
`FiniteExpectationInternalProof` structure only after the individual files
compile.

## 6. Milestone D: regular reals and effective limits

File: `lean/RegularExpectation.lean`.

Reuse the CLT packet's interval-name convention:

```lean
structure Regular where
  lo hi : Nat -> Rat
  ordered : ...
  nestedLo : ...
  nestedHi : ...
  width : ...
```

Add a refining finite-simple-law name:

```lean
structure L1SimpleName where
  level : Nat -> FinLaw
  parent : ...
  value : ...
  massRefines : ...
  l1Coherent : forall p m, p <= m -> l1Dist ... <= 2^(-p)
```

Construct `expectName`, prove it is regular, and lift finite linearity,
monotonicity, absolute-value bounds, and LOTUS.  All proofs reduce to a finite
level selected from the requested precision.

## 7. Milestone E: series and integration libraries

Implement in this order:

1. absolutely summable rational series with a tail modulus;
2. regular `ln`, reciprocal, `exp`, and rational powers by bisection/Taylor
   bounds;
3. compact Riemann integration for piecewise Lipschitz names;
4. improper integrals with a tail modulus;
5. CDF and layer-cake constructions;
6. geometric, Poisson, exponential, Gaussian, Pareto, and Cauchy examples.

For every analytic theorem, the object-language sentence quantifies only over
natural codes and precision indices.  The function names and moduli are fixed
primitive-recursive symbols in the schema.

## 8. Milestone F: convergence and Fourier modules

1. Finite Fatou kernel using pointwise finite minima.
2. Uniform-integrability truncation inequality.
3. Effective dominated convergence from convergence-in-measure and UI moduli.
4. Finite cyclic Fourier inversion; only after that, effective continuous
   inversion with absolute-integrability and quadrature moduli.
5. Characteristic-function derivative estimate using a finite Taylor
   remainder.

## 9. Suggested file graph

```text
IPRADerivations/Probability/FiniteLaw.lean
IPRADerivations/Probability/Expectation.lean
IPRADerivations/Probability/TailSum.lean
IPRADerivations/Probability/Variance.lean
IPRADerivations/Probability/MarkovChebyshev.lean
IPRADerivations/Probability/CauchySchwarz.lean
IPRADerivations/Probability/Independence.lean
IPRADerivations/Probability/Conditional.lean
IPRADerivations/Probability/SampleMean.lean
IPRADerivations/Probability/Kolmogorov.lean
IPRADerivations/Probability/RegularExpectation.lean
IPRADerivations/Probability/Series.lean
IPRADerivations/Probability/Integration.lean
IPRADerivations/Probability/Distributions.lean
IPRADerivations/Probability/Convergence.lean
IPRADerivations/Probability/Fourier.lean
```

Build one module at a time, as required by the repository's memory guidance.

## 10. Completion criterion

The project is complete only when:

- all ambient files compile with the repository's pinned Lean/Mathlib;
- all PR encoders/evaluators have proved defining equations;
- every main theorem has an explicit `Prf PRAAx` derivation, not merely a
  standard-model theorem;
- no theorem is introduced as an axiom or hidden behind `sorry`;
- the native translation is obtained through the existing proved bridge;
- the exact validation script remains a test suite, not part of the trusted
  theorem boundary.
