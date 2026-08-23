# Fabius function

This project formalizes the Fabius function and the results in both papers by
Juan Arias de Reyna:

- [*An infinitely differentiable function with compact support: Definition
  and Properties*](https://arxiv.org/abs/1702.05442);
- [*Arithmetic of the Fabius function*](https://arxiv.org/abs/1702.06487),
  version 3.

The development contains executable exact arithmetic.  The evaluator and its
analytic correctness at every dyadic, the canonical function's existence and
uniqueness, the moment and denominator arithmetic, the global differential
identities, Taylor reduction, the Fourier and entire-series identities,
probability and weak-convergence constructions, polynomial step
approximants, Poisson summation, and every theorem, lemma, corollary, and
prose proposition in both papers are checked without `sorry`.

## Design

The formalization separates two functions that the sources both call `F`:

- `BoundedFabius = ℝ → Set.Icc 0 1` is the CDF-style function requested for
  this project.  `IsFabius F` says that it is zero on `(-∞,0]`, one on
  `[1,∞)`, smooth, symmetric on `[0,1]`, and satisfies the differential
  equation on `[0,1/2]`.  The existence/uniqueness theorem selects the
  canonical `fabius`, constructed as the fixed point of an integral
  contraction on continuous symmetric unit-interval-valued functions.
- `extendedFabius F : ℝ → ℝ` is the signed global extension used in the
  paper.  It is defined by the locally finite Thue--Morse translate sum in
  equation (1).  It agrees with the bounded function on `[0,1]` but can be
  negative outside it.

The arithmetic layer is independent of real analysis:

- `moment`, `halfMoment : ℕ → ℚ` are the rational sequences `c_n`, `d_n`.
- `momentNumerator`, `halfMomentNumerator : ℕ → ℕ` are `F_n`, `G_n`, defined
  by division-free recurrences.
- `fabiusDyadicValue n a : ℚ` computes the bounded Fabius function exactly at
  the signed dyadic argument `a / 2^n`; `extendedFabiusDyadicValue` computes
  the paper's signed global extension.
- `evalFabiusDyadic : ℚ → Option ℚ` is the convenient rational-input wrapper.
  It returns `none` exactly when the reduced denominator is not a power of two.
- `fabiusDyadic` remains the independent closed formula from equation (32),
  while `rvachevDyadic` evaluates exact dyadic values of `up`.
- `reshetnikov : ℕ → ℚ` remains rational until its integrality is proved.
- `dyadicDenominator : ℕ → ℕ` is the finite LCM `D_n`.

This makes denominator, divisibility, parity, and valuation proofs live in
`ℚ` and `ℕ`; named bridge theorems connect them to the analytic functions.
The Fourier transform, sinc product, inversion integral, moment series, and
complex exponential generating function are also represented explicitly.

## Exact dyadic evaluation

The executable evaluator follows
[Reshetnikov's algorithm](https://mathematica.stackexchange.com/a/137749),
which is Proposition 10 of the paper in computational form.  It precomputes
the values `F(2^-k)`, removes one highest set bit from the numerator at each
step, and evaluates the resulting Taylor polynomial in Horner form.  Thus it
uses roughly `O(n^2 + n * binaryWeight(a))` rational operations for `a / 2^n`,
rather than work proportional to the numerator itself.  The rational-input
wrapper is the preferred front door because Lean's `ℚ` representation first
reduces inputs such as `10/32` to `5/16`.

`DyadicCorrectness.lean` proves termination, clamping, table-prefix stability,
refinement invariance, and representation independence.  The inverse-power
table is connected axiom-cleanly to the executable moment recurrences in
`MomentPowerSeries.lean`; `DyadicClosedForm.lean` proves the highest-bit Taylor
identity, and `DyadicAnalytic.lean` proves equality with every bounded analytic
Fabius function.  `GlobalDyadic.lean` supplies the corresponding proofs for
the signed global extension and for equation (32) on its full `[0,2]` range.

```lean
#eval Fabius.fabiusDyadicValue 4 5
-- 305857 / 2073600

#eval Fabius.evalFabiusDyadic (5 / 16 : ℚ)
-- some (305857 / 2073600)

#eval Fabius.evalFabiusDyadic (2 / 3 : ℚ)
-- none
```

Under the bounded convention, nonpositive inputs evaluate to `0` and inputs
at least `1` evaluate to `1`.  The separate global evaluator retains the
paper's oscillating continuation, for example `F(3) = -1`.

## Paper coverage

`Paper05442.lean` is the public import for the first paper.  It includes all
seven theorems, Lemma 1, the unnumbered non-analyticity corollary, and the
prose probability proposition.  In particular, it proves the original
existence-and-uniqueness characterization with the initially unknown scale,
weak-* convergence of the finite convolution measures, pointwise convergence
of the polynomial step approximants, the infinite-product probability model,
the differential identities, Poisson summation, moment formulas, and global
rationality at dyadic points.

`Paper06487.lean` is the public import for the arithmetic paper.
`PaperStatements.lean` contains all 18 proved numbered results in the v3 PDF:
Propositions 1, 2, 3, 4, 6, 8, 10, 15, 18, 19, and 22; Theorems 7, 9, 13,
17, 20, and 21; and Lemma 1.  It also formalizes Question 5, Definition 12,
and Conjecture 16.  `Paper06487Supplement.lean` proves assertions made in the
surrounding prose and inside proofs.

The exact source-to-Lean map is in [`PAPER_COVERAGE.md`](PAPER_COVERAGE.md).

The source contains a few statements that are not literally correct.  The
formalization records the mathematically valid versions next to their proofs.
Among them:

1. In the first paper, equation (12) must be a finite convolution; the printed
   infinite upper index is incompatible with its dependence on `m`.
2. The closed interval indicators in Theorem 2 double-count shared endpoints.
   `halfEndpointIntervalIndicator` gives endpoints weight `1/2`, preserving
   the asserted normalization `φ_n(0) = 1` and the pointwise limit.
3. Equation (25) omits `t` from its exponential, equation (26) needs `n > 0`,
   and equation (32) has inconsistent scaling.  The Poisson-summation module
   proves the corrected identities.
4. In the arithmetic paper, Lemma 1 is false for a negative scale and an
   arbitrary derivative order.  Its proof requires
   `0 ≤ scale + order`; the Lean statement includes that hypothesis.
5. Proposition 2's quotient `(exp x - 1) / x` has a removable singularity;
   `expm1Div 0` is defined to be `1`.
6. The exponent in `R_n` is positive in equation (27), its proof, and its
   displayed values.  The development uses that consistent positive exponent.

## Checking

From the repository root:

```sh
lake build FabiusFunction
```
