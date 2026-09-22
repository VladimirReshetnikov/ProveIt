# Mathematical review checklist

This document identifies the points most important for independent review.
It records the argument's scope, not an external certification.

## Load-bearing hypotheses

1. All supports in a single construction are sets. Perturbation supports are
   well ordered and strictly positive. Nonzero Gamma is essential for the
   necessity direction of the universal classification.
2. The analytic linearization theorem has an EXACT diagonal unitary multiplier;
   the positive perturbation has no constant or linear coordinate terms.
   The normalized conjugacy likewise has exact value zero and derivative I.
3. A fixed polydisk has finite positive radius. Entire coefficients are a
   different row in the classification. Radius-free germs are not common-domain
   germs.
4. Nonresonance means lambda^alpha != lambda_j for every |alpha| >= 2.
5. All scalar Hahn coefficients are constant under coordinate differentiation.
6. The centralizer domain is connected and one-dimensional; the map is
   nonidentity. The scalar time condition is v(c) + v(a) > 0.
7. The finite-order decomposition requires Lambda^q = I, not just the
   existence of some resonances.

## Critical proof steps

**Support finiteness.** Higman's lemma gives finitely many ordered positive
support words of each weight, and a well-ordered generated monoid. This is
stronger than a bound v(T^k A) >= v(A) + k min(S), which is not cofinal in a
higher-rank value group. Arbitrary input supports are handled by Lemma 3.2.

**Substitution inverse.** The geometric inverse of a pullback is multiplicative.
Its coordinate images define a positive map. At each Hahn coefficient the
operators are finite-order differential operators, so agreement on polynomial
jets proves that this inverse operator is the map's pullback.

**Logarithm is a vector field.** Polynomial interpolation in an ordinary time
parameter proves Leibniz. Each fixed-weight coefficient is a finite-order
differential operator, so Leibniz reduces it to its first-order coordinate
vector field. No assertion about arbitrary noncontinuous derivations is used.

**Fixed-point scheme.** The explicit matrix B = I + positive satisfies
Phi_c - id = B(ca). Its inverse is a strong matrix Neumann series. This proves
ideal equality directly; equality of zero sets is not substituted for it.

**Centralizer.** Commuting pullbacks have commuting positive logarithms. In
one variable, ab' - ba' = 0; division in the meromorphic Hahn coefficient field
and connectedness force b/a to be a Hahn scalar. This does not classify
higher-dimensional vector-field centralizers.

**Nonlinear linearization.** With F fixed, Schroeder's equation is linear in
the unknown h: (L + N_f)h = -f. The operator N_f adds positive support. Its
Neumann inverse therefore uses finitely many homological inversions at one
Hahn weight, even with infinitely many smaller unrelated weights.

**Analytic thresholds.** A single L inverse loses at most exp(-tau) in isotropic
Taylor radius. Finite depth therefore suffices for separate germs when tau is
finite, and for a fixed unchanged disk when tau is zero. Entire coefficients
remain entire through finitely many such inversions when tau is finite.

**Necessity.** For f = t^eta phi, every normalized positive conjugacy must
have h_eta = -L^(-1)phi and no coefficients below eta. Sparse ordinary analytic
phi makes this fail in the desired category. Later Hahn weights or an enlarged
workspace cannot repair this first coefficient.

**No unwarranted conclusion at intermediate tau.** The bound
rho(h_gamma) >= R exp(-ell_S(gamma) tau) is only a lower bound. It does not
prove that there is no common smaller radius when 0 < tau < infinity.

**Classical comparison.** Non-Brjuno quadratic non-linearizability is an
external theorem of the classical literature. The arithmetic construction
showing non-Brjuno with tau = 0 is proved in Section 10. Strong summability at
finite halo points must not be confused with ordinary convergence after
numerical specialization or at a critical infinite scale.

## What the 21 exact checks do not establish

They do not check arbitrary well-ordered supports, analytic radius bounds,
continued-fraction asymptotics, the universal quantifiers, priority, or every
hypothesis of the general statements. They check finite polynomial identities
in an explicitly truncated parameter algebra. There is no Lean verification
and no claim of independent peer review.
