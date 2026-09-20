# Scope, verification, and priority

## Established by the arguments in the article

1. The explicitly defined cubic F is an odd increasing homeomorphism R→R,
   is globally bi-Lipschitz, satisfies F^{∘3}=8 id, and has minimal
   iterative polynomial z^3-8. This is a counterexample to the proposed
   general root deletion in Draga–Morawiec Problem 6.1.
2. The analytic conjugate of translation has minimal polynomial
   (z-1)^2(z^2+1) and fails the corresponding real-only equation.
   The assertion is real analyticity on R, not a globally entire complex inverse.
3. Theorem 6.1 gives necessary and sufficient root-multiplicity conditions
   for minimal iterative polynomials of increasing homeomorphisms when
   every characteristic root has one common positive modulus.
4. Sections 7–9 prove quantitative realizations, sharp increasing-solution
   rigidity criteria in this setting, and fixed-point regularity results.

These are mathematical claims supported by the self-contained written
proofs. They are not being described as independently reviewed theorems.

## Exact computations actually performed

- 4,026 distinct rational test points for the cubic construction.
- Cubic identity, scaling, oddness, independent conjugacy agreement, and
  inverse checks at those points.
- 4,025 exact adjacent secant-slope checks.
- 161 recurrence checks per sample orbit, for n=-80,...,80, in four examples.
- Four nonzero exact Hankel determinants, including -56 for the cubic and
  1 for the analytic quartic.
- All arithmetic in `verify.py` is rational Fraction arithmetic.

The determinants are finite exact minimal-order certificates once the
all-index recurrence is proved. The finite recurrence and function samples
alone do not prove a statement for every integer or real input.

## Numerical computations actually performed

The separate bisection demonstration samples 2,001 real inputs in [-10,10].
Its small double-precision residuals illustrate the analytic example. They
are neither interval-arithmetic enclosures nor proof certificates. Their
last digits may vary across systems. Plotting is optional.

## Literature and originality

The original problem statement, its surrounding interpretation, and the
preprint page carrying it were checked. The problem was published in a
2016 journal article; its available v2 preprint is dated 1 December 2015.
Relevant later work was also located. No earlier explicit answer was found
in the retrieved material, but the search was not exhaustive.

Accordingly, this package makes no first-discovery claim. It does not
certify that the question was still unsolved anywhere on 20 September 2026.
Nonlinear conjugates and iterative roots are familiar constructions;
this package does not claim to invent the method.

## Not established here

- A classification of decreasing solutions.
- A classification when roots have different moduli.
- A full answer to Petrov's general linearity question.
- A classification on arbitrary proper real intervals.
- A classification for zero constant coefficient, where injectivity may fail.
- Formal proof-assistant verification or independent peer review.

## Selection and exclusion

The first entropy-backed draw chose area 18 of 80, Functional equations.
The complete supplied 71-entry manifest was reviewed. The target of this
article is not one of its listed problems. The original manifest is
unchanged, and its SHA-256 is recorded in `data/selection.json`.
