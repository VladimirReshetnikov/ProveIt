# Independent review: arithmetic foundations and Dirichlet realization

Reviewed the initial contents of:

- `paper/sections/02_foundations.tex`
- `paper/sections/04_dirichlet_arithmetic.tex`

I checked the numerical constants and, separately, the claimed elimination
of infinitary reasoning. The quantitative Dirichlet proof itself had already
been independently audited.

## Definite corrections

1. The local-error formula
   `2^{-r-b-3}/(m+1)L^{m+1}` is ambiguous and conventionally means division
   by `m+1` followed by multiplication by `L^{m+1}`. It must be
   `\frac{2^{-r-b-3}}{(m+1)L^{m+1}}`.

2. The integral-coefficient tail contains `2q,2^j`. Replace its comma by
   multiplication spacing: `2q\,2^j`.

3. The list of analytic cutoffs claimed to be exhaustive but gave no cutoff
   for computing L' on [1,2]. A convenient uniform bound is

       tail(L', N) <= q(2 log N + 3)/N <= 5q/sqrt(N).

   Thus `N=2^{2(r+6)}(q+1)^2` leaves a tail below `2^{-r-3}`.
   The sharper exact integration bound is `q(log N+2)/N`, but is unnecessary.

The logarithm approximation, exponential cutoff, rational-gap lemma,
coefficient tails, quadrature constant J, Euler-log cutoff, and logarithmic
derivative bound 288 q^4 delta^(-2) all checked out. Their constants have
substantial slack.

## Substantive initial gaps and supplied repairs

### A. Complex roots need a compatible numerical realization

The original paragraph proposed both an exact cyclotomic field and
sine/cosine approximations, but did not prove that the numerical name was a
primitive root satisfying the symbolic identities. Invoking irreducibility
of the cyclotomic polynomial also introduced an unnecessary lemma package.

I supplied the following direct repair to the parent. Define

    A(x) = integral_0^x (1+t^2)^(-1) dt,  0<=x<=1,
    pi = 4 A(1).

Finite geometric integration identifies A(1) with the alternating
arctangent series. For

    R(x)=exp(2 i A(x)) (1-i x)/(1+i x),

the formal derivative cancels; the denominator is bounded away from zero.
For example the component bounds |F'|<=2, |F''|<=8, |G'|<=2, |G''|<=4
give |R''|<=20. A finite telescoping residual argument then gives R(x)=1,
so exp(2i A(1))=i and exp(2pi i)=1.

Eight alternating terms give pi>3, and pi<4 follows from its integral.
Pairing the sine series gives sin t>=t-t^3/6>=t/3 for 0<=t<=2.
Therefore, for zeta_h=exp(2pi i/h),

    |zeta_h^k-1| >= 2/h,  1<=k<h.

To see this, reflect k to m=min(k,h-k), put t=pi m/h<=pi/2<2,
and use |exp(2it)-1|=2 sin t and t>=3/h. This gives primitive recursive
names, exact multiplication and unit norm, and an explicit separation
margin. Orthogonality cancellation can use that margin; no unbounded
numerical search or cyclotomic irreducibility theorem is needed.

### B. The coefficient identity needed more than an assertion about differentiation

The original sentence about differentiating finite partial-summation
identities did not give a complete finite argument for the product
coefficients. I wrote the detailed replacement:

    paper/sections/04b_jet.tex

It proves the identity by finite summation by parts and an N-by-N
convolution rectangle. Terms with uv<=N give the exact divisor sum c_j(N);
the remaining rectangle terms have the same positive tail bound used for
c_j. Hence no rearrangement of an infinite double sum or differentiation
of an unspecified limit is needed.

The addendum supplies:

- moment tails `2*4^j*N^(-3/4)`;
- the endpoint term `q*4^j*N^(-7/4)`;
- finite moment recurrences for the integrals with t^(-2) and t^(-3);
- a common cutoff with all error amplification accounted for;
- the equality epsilon=sum l_j, proved using a finite exponential
  polynomial on [1,N] whose entire integral tail is <=3q/N independently
  of its polynomial degree;
- a bounded rational array invariant, with the accuracy fixed as an
  external parameter before induction.

### C. Avoid a hidden mean-value theorem

A statement that an integrand has a derivative bounded by J is not by
itself a license to import a general constructive mean-value or Rolle
theorem. For the specific elementary expressions used here, write the
finite telescoping rule explicitly:

    If every rational mesh cell has
    |f(x+h)-f(x)-h g(x)| <= M h^2 + epsilon,
    then N equal cells over [a,b] give total error
    <= M(b-a)^2/N + N epsilon.

This is literally a finite sum identity and triangle inequality. The
geometric identities for log, finite binomial expansion and tails for
exp, reciprocal identity with a denominator margin, and finite product
rules provide the increment residuals for the expressions actually used.
This suffices for the arctangent construction, quadrature, and finite
integration by parts without importing a general real-analysis theorem.

Case splits on comparison of a real variable with a rational threshold
should be interpreted on the rational mesh inputs actually required, or
replaced by overlapping thresholds. Arbitrary real order is not decidable.

## Assessment of the “second level” claim

The original two sections alone supplied a detailed quantitative blueprint,
but asserted two nontrivial compatibility steps: roots of unity and product
coefficients. Their explicit repairs above, together with the finite
increment/telescoping rule, make the human-level arithmetic realization
credible: the induction invariants are rational equations/inequalities with
bounded index assertions; precision is a parameter, not a quantifier inside
the induction formula.

The report should keep its existing clear separation between such a human
arithmetic derivation and an actual checked `Prf PRAAx` object. The latter
has not been constructed. Primitive recursiveness of the algorithms alone
would not have proved the former; the finite identities and invariants are
the essential additional work.

## Additional sharp Brun–Titchmarsh audit

At the parent's request I also checked `research_sieve/sharp_core.md` and
`research_sieve/sharp_completion.md`. The following all checked out:

- disjoint-interval argument and convex midpoint integral estimates;
- mixed cosecant-square identity and the sign of its logarithmic term;
- all added-index signs in U,V and their eigenvector cancellation;
- residual correction for an approximate eigenvector;
- weighted Cauchy and the constants in `E^2<=24/pi^4+16E/pi^2`;
- finite-grid maximum and residual test;
- weighted large-sieve duality and the Ramanujan-sum insertion;
- the q/phi(q) decreasing-weight comparison;
- the G(z) and J(z) partial-summation constants;
- the integer-floor sieve endpoint and the large-ratio inequalities;
- the small-ratio monotonicity argument and overlapping coverage.

For the finite-grid estimate, rounding a unit vector has error at most
2Rh, normalization error at most 4Rh, and Rayleigh loss at most 8R^2h.
The matrix perturbation adds at most 2Rh. Hence h=tau/(100R^2) is sufficient
with ample slack.

The supplied rational certificate used Machin's identity for pi. I
recommended using 100 alternating terms at atan(1) instead, consistent with
the foundation's pi definition and needing no extra angle identity.
An exact Fraction calculation confirmed that these terms give lower>31/10
and upper^2<10. This is an optional simplification, not a defect in the
classical Machin identity.
