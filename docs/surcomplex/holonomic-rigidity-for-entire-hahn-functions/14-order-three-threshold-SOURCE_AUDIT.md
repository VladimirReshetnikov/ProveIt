# Source, novelty, and proof audit

Date: 23 September 2026.

## Requested sources and fixed baseline

The user's repository was inspected through its connected GitHub interface:

- Repository: https://github.com/VladimirReshetnikov/Surreal
- Main snapshot: `b895e8672990e8b5a56f97dd7246f9dd5f86c771`
- Inspected root README and repository tree.
- Inspected `docs/README.md`, including research-report and verification boundaries.
- Inspected `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`.
- Inspected adjacent report inventories to distinguish already-covered directions.

The much larger formalization ledger did not return text through the attempted
file fetch; no assertion of a complete audit of that ledger is made. The new
proof is not represented as covered by the repository's existing Lean build.
The Wikipedia surreal-number article supplied by the user was consulted as
orientation; technical normal-form background is attributed to the primary
Mantova–Matusinski survey instead.

## Actual prior project manuscript

The earlier saved manuscript was retrieved from the user's file library:

- Title: *Theta Descent and the Exact Boundary of Differential Rigidity*.
- Date: 23 September 2026.
- LaTeX filename: `article(20260923-193210).tex`.
- Earlier PDF filename: `article(20260923-193208).pdf`.
- Its repository baseline: `4cdeaec43ff1692ed2ad9f5bdf761a41872975a5`.
- The exact unresolved question is source label `q:order2`.

The inspected source includes the explicit order-two question, Chebyshev
coefficient formulas, the theta differential equation and normalization proof,
the no-order-unit argument, and its statements of scope and provenance.
The prior manuscript proves minimum order three for its particular theta
example. It expressly does not exclude order two for every other example.
That latter universal exclusion is the main result of the new article.

The earlier manuscript is not redistributed in this package. The new article
is self-contained and credits it as an unpublished project source, not as a
peer-reviewed publication.

## Primary public sources checked

1. NIST DLMF §20.5 — Jacobi products and logarithmic derivatives:
   https://dlmf.nist.gov/20.5
2. NIST DLMF §23.3 — Weierstrass differential equation:
   https://dlmf.nist.gov/23.3
3. NIST DLMF §32.2 — Painlevé equations:
   https://dlmf.nist.gov/32.2
4. Mantova and Matusinski, *Surreal numbers with derivation, Hardy fields and
   transseries: a survey*, arXiv:1608.03413v2:
   https://arxiv.org/html/1608.03413v2
5. Ahmed Sebbar, *Finite and Infinite Order Differential Relations for Theta
   Functions*, Milan Journal of Mathematics 84 (2016), 317–347:
   https://link.springer.com/article/10.1007/s00032-016-0261-6
   Publisher abstract inspected; full subscription text not inspected.

The theta product and elliptic differential identity are classical. Their
normalization and formal specialization are proved in the article, but no
priority claim is attached to those classical identities.

## Proposed contributions versus inherited results

**Proposed new results:** universal second-order rigidity over arbitrary
ordered-group rank in characteristic-zero Hahn fields; the finite endpoint
spectrum after removing degenerate logarithmic factors; the third-order
endpoint–gap obstruction; the exact classification of theta initial
polynomials; eventual nonvanishing and strict convexity of coefficient
valuations for any nonpolynomial strongly entire solution of the fixed theta
residue-type equation; the stated low-dimensional-system consequences.

**Inherited and explicitly credited:** the theta descent, its entire
order-unit case, its order-three relation, its zeros and omnific rounding;
the no-order-unit all-order obstruction; the coefficient-field principle
used in that obstruction; Hahn and surreal normal-form background.

**A new combined conclusion:** among all nonpolynomial strongly entire
functions, the minimum differential order is exactly three when an order unit
exists. The new part is the universal exclusion of order two, not the prior
existence witness.

## Literature search limitations

Targeted searches considered second-order algebraic differential equations,
Hahn entire functions, non-Archimedean rigidity, and classical theta
differential relations. Several results referred to Hahn difference operators
or unrelated non-Archimedean stability questions. These are not evidence that
an equivalent theorem does not exist in the literature.

No exhaustive MathSciNet/zbMATH search, full subscription-literature review,
independent peer review, or global audit of every repository branch was
performed. Bibliographic priority remains unverified.

## Mathematical checkpoints

- The all-scale criterion does not confuse one strongly summable family with
  cofinal decay; necessity deliberately uses a second, more exterior input.
- Divisibility is introduced only by a cofinal extension, then removed.
- Infinite Newton envelopes are used only through finite envelopes on bounded
  radius intervals.
- Exterior dominance is proved by an explicit finite coefficient inequality.
- The homogeneous jet polynomial is nonzero even when its monomial symbol is
  identically zero.
- Removing the highest power of the logarithmic derivative before endpoint
  evaluation is essential to the second-order proof.
- Positive characteristic is excluded and an explicit counterexample is given.
- The theta initial-form classification is a rational-function proof, not an
  extrapolation from the finite enumeration.
- Eventual strict Newton convexity is only a necessary condition on full
  solutions; no sufficiency or complete global classification is claimed.
- Strong entireness is field-relative and uses the external variable derivative.

## Computational boundary

The exact program checks 600 finite algebraic statements. Its q-adic identity
checks are modulo q^48 with coefficients in Q[z]. They cannot certify the
infinite support arguments or the universal theorems. The package contains no
new Lean theorem claimed to have been compiled.
