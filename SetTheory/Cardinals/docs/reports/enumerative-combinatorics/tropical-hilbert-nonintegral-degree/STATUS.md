# Status of the mathematical claims

Date: 20 September 2026.

## Complete proposed resolution

The article supplies a self-contained proof of

    TH_{V_d}(k) = k + min(k, ceil(k/d)) + 1

for every positive rational d and every nonnegative integer k, where V_d is
the displayed union of two horizontal unit segments. The result is for the
strict-witness definition and total-degree cutoff of Definitions 1.1–1.2 of
Grigoriev, arXiv:2404.06440v2.

The special case d=3 has degree 4/3 and exact least quasipolynomial period 3.
This refutes both integrality and eventual polynomiality for that definition
on the source's stated class of min-plus prevarieties. The analogous box
result is separately proved for d >= 1, so the d=3 counterexample also works
for that convention.

## Proven consequences

- Every rational number in (1,2] is realized as a tropical degree by this family.
- The reduced denominators of such degrees are unbounded.
- At d=p/q>1 in lowest terms, the least eventual quasipolynomial period is p.
- At 0<d<=1 the total-degree function is the polynomial 2k+1.
- For d=3 the generating function is (1+z)^2 / ((1-z)(1-z^3)).
- All optimal lower-bound supports come with explicitly specified rational
  coefficients and witnesses. The proof handles k=0 separately.

## Source and novelty limitations

The latest primary version retrieved still states the integrality question
and the eventual-polynomiality conjecture. Targeted web searches did not
locate a subsequent resolution. This is not an exhaustive priority claim:
unindexed, privately circulated, or concurrent proofs may exist.

The source's definitions and questions are attributed to it. No claim is made
that tropical Hilbert functions themselves are newly introduced here.
The new claim of this package is the displayed exact two-segment computation
and its consequences, subject to independent review.

The uploaded 71-entry manifest was read in full and none of its listed
problems was selected. Its claims were treated as exclusions, not reverified.
The original random area draw was 50 of 96, Tropical geometry, with no redraw.

## Verification limitations

The proofs have not been checked in Lean or another proof assistant, and have
not been independently refereed. Exact finite checks passed, including
823,974 strict witness inequalities. They corroborate the formulas and verify
individual certificates; they are not a substitute for the all-degree proof.

The upper-bound enumeration is a relaxation of necessary endpoint conditions,
not an enumeration of all tropical polynomials or a general decision algorithm.

## Not claimed

No general theorem about connected or balanced tropical curves is claimed.
No contradiction with ideal-theoretic Hilbert-polynomial results is claimed.
No general rationality or quasipolynomiality theorem for arbitrary prevarieties
is claimed. No higher-dimensional limit problem is solved. No statement of
irrational tropical degree in the rational-polyhedral category is made.
