# Fabius function

This project formalizes the Fabius function and the statements in Juan Arias
de Reyna, [*Arithmetic of the Fabius function*](https://arxiv.org/abs/1702.06487),
version 3.

The development contains executable exact arithmetic and is now in its proof
completion phase.  The structural evaluator proofs, moment/half-moment
power-series bridge, normalized half-moment formula, monotonicity and strict
positivity, support calculations, and several paper results are checked
without `sorry`; the remaining analytic and arithmetic statements are being
discharged incrementally.

## Design

The formalization separates two functions that the sources both call `F`:

- `BoundedFabius = ℝ → Set.Icc 0 1` is the CDF-style function requested for
  this project.  `IsFabius F` says that it is zero on `(-∞,0]`, one on
  `[1,∞)`, smooth, symmetric on `[0,1]`, and satisfies the differential
  equation on `[0,1/2]`.  The existence/uniqueness theorem selects the
  canonical `fabius`; its construction remains on the current proof frontier.
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
`MomentPowerSeries.lean`.  The remaining exact evaluator step is the general
highest-bit Taylor identity connecting the fast recursion to equation (32),
followed by the analytic bridge from equation (32) to `fabiusReal`.

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

`PaperStatements.lean` contains all 18 proved numbered results in the v3 PDF:
Propositions 1, 2, 3, 4, 6, 8, 10, 15, 18, 19, and 22; Theorems 7, 9, 13,
17, 20, and 21; and Lemma 1.  It also formalizes Question 5, Definition 12,
and Conjecture 16.  Remarks 11 and 14 are expository and are documented but
do not receive theorem declarations.

Three source issues are made explicit:

1. The arXiv abstract gives a negative exponent in `R_n`, but equation (27),
   the proof, and the displayed values require the positive exponent used
   here.
2. Lemma 1 is false for a negative scale and arbitrary derivative order.  Its
   proof requires `0 ≤ scale + order`; the Lean statement includes it.
3. Proposition 2's quotient `(exp x - 1) / x` has a removable singularity.
   `expm1Div 0` is defined to be `1`.

## Checking

From the repository root:

```sh
lake build FabiusFunction
```
