# Fabius function

This project formalizes the Fabius function and the results in both papers by
Juan Arias de Reyna:

- [*An infinitely differentiable function with compact support: Definition
  and Properties*](https://arxiv.org/abs/1702.05442);
- [*Arithmetic of the Fabius function*](https://arxiv.org/abs/1702.06487),
  version 3.

It also gives a claim-level formal audit of the two local TeX drafts under
`Papers/`: *Fabius Asymptotic* and *K-fold summation over the signed
Thue-Morse sequence*.  Neither local draft contains a formal theorem, lemma,
proposition, or corollary environment, so their coverage is indexed by
numbered equations and substantive prose claims.  Some of those claims are
false or unsupported; the development records counterexamples and corrected
statements rather than asserting them.

The development contains executable exact arithmetic.  The evaluator and its
analytic correctness at every dyadic, the canonical function's existence and
uniqueness, the moment and denominator arithmetic, the global differential
identities, Taylor reduction, the Fourier and entire-series identities,
probability and weak-convergence constructions, polynomial step
approximants, Poisson summation, and every theorem, lemma, corollary, and
prose proposition in both papers are checked without `sorry`.  The asymptotic
layer additionally proves the corrected sharp small-argument expansion with
its nonconstant Gamma--zeta periodic term, together with its complete
all-orders saddle expansion.

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
the signed global extension and for equation (32) at every nonnegative dyadic
argument `m / 2^n`, with no restriction that the representation be reduced or
that `m ≤ 2^n`.

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

`PaperFabiusAsymptotic.lean` is the public aggregate for the first local
draft.  It proves the exact logarithmic delay equation, the elementary log
expansions, explicit dyadic bounds, the full-real quadratic leading term, and
the coarse `O(t * log t)` error.  It also proves that the draft's proposed
sharp main term has a nonzero `(log t / t)^2` equation residual and therefore
is not `O(t^-2)`.  The draft's unsupported periodic-in-`t` argument is not
used.  Independently, a negative-Laplace product, Mellin finite-part analysis,
and quantitative Bromwich saddle proof establish a corrected sharp formula
with error `O(1 / (-log x))`.  Its centered periodic correction is reconstructed
as an absolutely summable Gamma--zeta Fourier series and proved nonconstant.
More strongly, if `lambda = fabiusLambertPhase x`, then for every `N`

```text
log F(x) = fabiusSharpLambertMain x
  + sum (j < N), lambda^(-j) * fabiusSaddleLogCoefficient j lambda
  + O(lambda^(-N)).
```

The zeroth coefficient is zero, and the first explicit correction is
`fabiusFirstSaddleCorrection lambda / lambda`.  A separate theorem expands
`lambda` itself to arbitrary order in `-log x` and `log (-log x)`.  The full
formula keeps the oscillatory coefficient functions at the exact Lambert
phase; it does not silently replace them by a lower-order phase approximation.

The asymptotic aggregate also audits four linked Stack Exchange discussions.
The recurrence sequence is exposed directly as
`fabiusRecurrenceSequence n = halfMoment n / n!`, with its displayed
recurrence, Bernoulli recurrence, inverse-dyadic bridge, generating series,
and product all proved.  The
[conjectured finite q-binomial formula](https://math.stackexchange.com/questions/3283519/conjectured-formula-for-the-fabius-function)
is proved exactly in its full stated scope: for all natural `m,n`, its
half-shifted Thue--Morse sum is the signed global Fabius value at `m / 2^n`.
No condition `m ≤ 2^n` or irreducibility of the dyadic representation is
needed.  When `m ≤ 2^n`, the same formula is a corollary for every bounded
function satisfying `IsFabius`.  The rational expression is independent of
the representation of `m / 2^n` (in particular, it is unchanged by
`(m,n) ↦ (2m,n+1)`) and is invariant under any common rational translation
of its inner powers.  More explicitly, for every `q : ℚ` the fully displayed
sum with inner power `(j - m * 2^k + q)^(n+k)` has that same value; literal
rational, signed-global, and bounded-unit-interval theorems are public.
Thus the source's `+1/2` formula and the centered form agree, while its
`QPochhammer`/`QBinomial` factors retain notation-faithful public definitions.
For the inverse-power specialization, dyadic reflection additionally proves
for every `q : ℚ` the raw-coordinate formula with inner power
`(r+q)^(n+k)` and denominator `(-2)^(n^2)`.  Its fully literal theorem uses
the zero-one `thueMorseBit`; at `n = q = 0`, the sole inner power is `0^0`
and evaluates to one.

The global binary-reduction series is also formalized.  Its correct outer
index starts at `m = 0`, where `Floor[2^(m-1)x]` is genuinely `Floor[x/2]`.
For every real `x ≥ 0`, the series converges absolutely to the signed global
Fabius extension.  This specializes to the bounded Fabius function on
`0 ≤ x ≤ 1`.  The complete finite inner expression is a constant polynomial
in its common translation, so the theorem holds not only for rational `q`,
but for every real or complex `q`.  The missing `m = 0` term is zero on
`0 ≤ x < 1` and equals one at `x = 1`; this explains both why the former
one-indexed formula worked on the half-open interval and why it failed at the
right endpoint.  The primary public endpoints are
`Fabius.hasSum_qBinomialFabiusGlobalSummand`,
`Fabius.globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_real`, and
`Fabius.globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_complex`.

The generalized Wolfram `DiscreteLimit` formula is proved as well.  For every
real `x ≥ 0` and every `q : ℂ`, its finite q-binomial/Thue--Morse
approximants converge to the signed global Fabius value; on `[0,1]` the limit
is the ordinary bounded Fabius function.  Separate public specializations
cover rational shifts, Gaussian-rational shifts, and arbitrary real shifts,
including irrational ones.  Lean encodes the inner sum safely with length
`⌊2^(n+k) x + 1/2⌋₊`; `Fabius.fabiusDiscreteLimitRangeLength_eq_floor_add_one`
proves that this is exactly the successor of the inclusive Wolfram upper
bound `Floor[2^(n+k) x - 1/2]`, including its empty case.  A finite row can
genuinely depend on `q` at a nondyadic `x`; it is the limit that is independent
of every fixed complex `q`.  The proof reindexes each row as a uniformly
bounded Toeplitz average of centered finite Thue--Morse splines, proves their
global convergence through finite uniform-distribution CDFs, and controls a
complex shift by a decaying Taylor bound.  Finally, exact telescope and
`tsum` theorems identify the same limit with the binary-reduction series; they
do not assert a termwise equality between the two finite approximations.  The
primary endpoints are
`Fabius.fabiusDiscreteLimit_literal_complex_tendsto_globalFabius`,
`Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_fabiusReal`, and
`Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum`.

The recurrence sequence's fixed-constant heuristic
omits the nonconstant periodic correction.  The elementary small-`x`
expression from
[Math Stack Exchange](https://math.stackexchange.com/a/3925650/19661) is
formalized verbatim and corrected by adding that term at the exact
lower-Lambert phase.  The uncorrected claimed error is formally disproved.
Exponentiating the corrected formula gives a proved asymptotic equivalent for
the Fabius function itself.
Finally, the proposed
[quotient-of-exponentials fit](https://mathematica.stackexchange.com/questions/285919/approximation-of-the-fabius-function-with-a-quotient-of-exponentials)
is little-o of the true displaced Fabius bump at the endpoint, so it cannot be
an asymptotic equivalent despite its good compact-interval plot.

`PaperKFoldThueMorse.lean` is the public aggregate for the second local
draft.  It contains the exact prefix-sum, zero-run, convolution, and
generating-series identities; the intended real polygonal interpolation; and a
proved corrected pointwise approximation scheme.  It also exposes the
zero-one sequence `thueMorseBit` and proves the exact identity expressing it
through `Log2` of the signed binomial-parity sum.  The Stirling estimate used
by the draft is proved in its precise `O(log n)` form.  The aggregate also
exposes formal counterexamples to the literal normalization, the claimed local
and global error estimates, the unbounded “maximum” proxy, and the omitted
linear term in the subsequent Stirling calculation.  Both qualitative decay
comparisons are proved: the Fabius function is smaller than every power at
zero, while `exp (-c/x)` is little-o of it for every `c > 0`.  No Lambert-W
theorem is used to justify the false proxy chain; instead, the repaired lower
branch, its equation-(9) solution, and its standard two-term expansion are
proved separately.

The exact source-to-Lean map is in [`PAPER_COVERAGE.md`](PAPER_COVERAGE.md).
The requirement-by-requirement asymptotic evidence is recorded in
[`ASYMPTOTIC_COMPLETION_AUDIT.md`](ASYMPTOTIC_COMPLETION_AUDIT.md).

The two arXiv sources contain a few statements that are not literally correct.  The
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
