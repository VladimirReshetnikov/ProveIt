# Results and evidence ledger

## Proved in the article

**Signed-density theorem (Theorem 2.2).** For integer a >= 1 and real b > 0,
the density kappa_(a,b) has moments H_(n-1)^(b)/n^a, zero total mass, and exactly
one negative-to-positive sign change. Its Stieltjes-type integral continues
Li_(a,b)(z,1) to the slit plane.

**Unique-zero theorem (Theorem 3.1).** The imaginary part on the upper unit
semicircle has exactly one interior zero, simple and below pi/2, with positive
sign before the zero and negative sign after it. In particular every g_(a,b)
is strictly negative. The proof compares ratios of the angular kernels; it does
not rely on sampled plots or a numerical zero count.

**Zero asymptotic (Theorem 4.1).** The four terms in article equation (4.1)
are proved with remainder O((2/7)^a), uniformly for real b >= 1. Numerical
observations about the next coefficient are not an all-order proof.

**Parity specialization (Theorem 5.1).** This is a branch-safe specialization
of a known theorem of Panzer, including inner index 1. It proves the five
weight-six source candidates and generates all even-weight tables. This
package does not claim priority for the parity theorem.

**Same-point shuffle theorem (Theorem 6.1).** The matrix has rank floor(w/2)
in every weight and has an explicit normalized Pascal inverse. The source's
weight-five relation is the exact two-row consequence 960 R_(1,4) - 224 R_(2,3).
Two further weight-seven identities have supplied coefficient certificates.
The rank is formal; no period independence follows.

**Euler certificate (Theorem 7.1; Proposition 7.2).** All nonzero differences
have the same negative sign. The exact enclosure has width at most C_b*2^-N.
Binomial-tail weights allow linearly many exact updates; the bit complexity
is polynomial in precision at fixed indices.

**Exact kernel and sharp Euler error (Theorems 8.1 and 8.2).** The density is
a finite polynomial plus explicitly known polylogarithms. This yields the full
logarithmic error polynomial and the leading error
sqrt(pi)*2^-N*(log N)^(w-1) / (2^w*(w-1)!*sqrt(N)). The simple rigorous bound,
not the asymptotic approximation, is used in the evaluator.

**S-family certificate (Proposition 9.2).** The odd-denominator harmonic sums
have one-sided Euler tail bound (N+1)/(3^p*2^N). This certifies closeness of the
S4 candidate but does not prove equality.

**Finite module obstruction (Proposition 9.3).** A supplied rational vector
annihilates the specified 92-by-23 weight-five coefficient matrix but has dot
product one with the S4 target. Thus that restricted linear system cannot
prove the proposed identity by rational linear combination alone.

## Conjectural

**S4 evaluation (Conjecture 9.1).** Still unproved here. Its difference from
the proposed right side is rigorously enclosed in [-10^-118, 10^-118].

**Odd-weight matrix-rank pattern (Conjecture 9.4).** Exact ranks agree with the
stated formulas at all 15 odd weights 3 through 31. No extrapolation to a
theorem in all weights is made.

**Additional zero behavior.** Monotonicity in a and b, the full expansion,
and extensions to noninteger outer index remain research questions.

## Computational support

The default exact suite passes 588 check cases. All 64 generated even-weight
formulas through weight 16 receive an independent rational interval comparison.
Separate floating-point diagnostics cover 16 Euler-asymptotic cases, nine zero-
asymptotic cases, nine illustrative zero-table entries, and one S4 replay.

No formally checked Lean proof, exhaustive novelty certification, numerical
period-independence result, or complete historical-script replay is asserted.
