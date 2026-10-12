# Summation and singularities: proof review, 12 October 2026

The angular, Lambert and endpoint proofs have been read against the current
repository. Their conventional mathematical conclusions below are accepted
for collective synthesis. All delivered TeX, PDF, programs and recorded
outputs remain unchanged. Fresh executions are in `intake-verification`.

## Angular reversion and the order of summation

The positive two-variable kernel gives the stated moments and the uniform
small-disk estimate. Rouche then proves existence of the selected angular
zero and convergence of its auxiliary Lagrange series. At radius one,
each fixed-degree inner Fourier expression is interpreted by its Abel
limit before summing the absolutely convergent outer series. This does
not license arbitrary rearrangement of the old base-grouped multiset
series: the prime-frequency obstruction to that rearrangement survives.
The negative-index lowering formula yields a finite period algebra for
integer orders; it makes no independence or minimal-basis claim.
The moving finite cutoff proves the stated attainable quadratic exponent,
not optimality of that exponent.

## Lambert inverse conjecture and first correction

The equation includes the linear forward term r_1=-1/4. Keeping it produces
the two exponential amplitudes exp(-Au/4) and exp(Au/4), A=4*pi^2.
The proof controls the entire Lagrange sum: factorial convolution gives a
summable majorant below k=n/2 and a superalgebraically small upper tail.
Thus the one-large-index calculation is uniform on compact complex u
sets, rather than only a calculation at fixed factor count.

This proves the named even/odd conjectures of the parent report
(`article.tex`, labels `eq:conj-even` and `eq:conj-odd`). The explicit
1/n correction also accounts for the nonlinear core and the small r_2
configuration. The additive complex formulation remains valid when a
hyperbolic parity amplitude vanishes. The analytic-core universality
theorem requires the stated common analytic neighborhood on compact
parameter sets.

The logarithmic Borel model has a continuous remainder on the closed
initial disk; adding the dilogarithm terms gives a remainder with continuous
first derivative. The nonzero exponential action amplitudes prove genuine
singularities at both endpoints for every fixed u != 0, exact Borel radius
A, and ordinary radius zero. These arguments alone do not prove analytic
continuation beyond the initial disk or identify a full local alien germ.
The newly arrived *Sharp Late Coefficients and Borel Continuation of
Resonant Lambert Inverses* overlaps this result and claims additional
continuation through a cited closure theorem; that extra claim has a
separate audit and is not certified by the present review.

## Direct inverse endpoints

For nonintegral s>1, write s-1=p/q in lowest terms when rational. The
minimal cover degree is min(p,q); irrational s-1 and integral s>=2
admit no finite cover. The endpoint is holomorphic precisely at
s=1+1/q, q>=2. At these orders the convergent auxiliary inverse gives
the coefficient formula and support inclusion q+<q-1,q>. That inclusion
does not assert that every allowed coefficient is nonzero.

The proposed extension of the integer-order cut-modulus assertion fails
locally for 1<s<3/2. This is a correction to a suggested extension, not
to the proved integer-order result. Endpoint classification is local;
it does not determine the global inverse Taylor radius.

## Fresh finite evidence

All three delivered verification scripts completed successfully on separate
copies using Python 3.13, SymPy 1.14.0 and mpmath 1.3.0. The angular suite
checks the first four exact degree polynomials, rational constants and
85-digit root/cutoff diagnostics. The Lambert suite computes all finite
Lagrange summands for 40 cases through n=201 at 90 working digits, including
complex coupling and a parity cancellation. The endpoint suite checks
15 exact coefficients, four inverse-root comparisons and four cut-bank
diagnostics. Table and figure generation also completed using the fresh
JSON outputs. No floating-point comparison is an interval certificate.

The fresh tables are retained with the JSON and logs. Generated diagnostic
figures were exercised on the replay copy; the authored figures and PDF
remain original. No collective volume was rebuilt by this audit, and no
Lean formalization is claimed. The all-inverse-index-order question remains
open in this source; the current correction compiler is separate ongoing
research until its uniform remainder proof is written and reviewed.


## Canonical all-order extension, 12 October 2026

The subsequent [Volume I section](../../../../../../Polylogarithms/docs/manuscript/chapters/01-lambert-late-coefficients.tex) now supplies the written
uniform remainder argument and finite Faulhaber/Poisson correction formula
for every fixed order. Theorem 1.26 resolves the all-order question noted
above, and gives higher-polylogarithm boundary models. Its compiler checks
through order four; the explicit second correction also has a separate
small-multiset calculation in the text. This supersedes the earlier
research-status sentence without changing the delivered article. Global
continuation and a full local alien description remain separate questions.
