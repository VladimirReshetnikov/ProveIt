# Sources, scope, and novelty record

Date: 23 September 2026.
Pinned repository: https://github.com/VladimirReshetnikov/Surreal
Commit: bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59

## Repository material inspected

The root README, recursive tree and docs/README.md were read to locate relevant
work. Focused documentation reads were then made for:

1. `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/`
   Directory listing, catalogue description and
   `12-coefficient-field-rigidity-SOURCE_AUDIT.md`.
   The latter records no-order-unit all-order rigidity, finite coefficient-field
   restrictions, and the remaining general pure-differential order-unit case.
2. `docs/surreal/tail-spans-and-differential-transcendence/README.md`.
   Existing cofinite-span classification, square-root coefficient witnesses,
   numerical BM jets, analytic mixed derivatives on a fixed ordinary disk,
   almost-disjoint families, and explicit limitations on point evaluation.
3. `docs/surreal/transcendence-over-bounded-support/README.md`.
   Existing separated-support algebraic freedom, factorial-height integer
   witnesses, bounded-support descent, normal-form realizations, and the
   explicit absence of a differential-independence claim in that report.

No exhaustive line-by-line review of all 57 catalogued reports, their histories,
or the Lean declarations was performed. README claims are recorded as repository
claims, not independent proof verification. The present manuscript reproves the
bounded-support descent fact it needs and proves its finite algebraic core
without importing the repository's main differential theorems.

## Primary external sources inspected

- Alessandro Berarducci and Vincenzo Mantova, *Surreal numbers, derivations and
  transseries*, J. Eur. Math. Soc. 20 (2018), 339–390,
  doi:10.4171/JEMS/769.
  https://arxiv.org/html/1503.00315v3
  Inspected the normal-form/summability conventions and the introduction's
  Theorem A and normalization of the simplest derivation at omega.
- Olivier Bournez and Quentin Guilmant, *Surreal fields stable under exponential
  and logarithmic functions*.
  https://arxiv.org/html/2201.08199v1
  Section 2.3.4 explicitly identifies t^a with omega^(-a).
- Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
  power series and omnific integers*.
  https://arxiv.org/html/1710.07304v5
  Section 1.1 provides the normal-form definition of Oz. No factorization
  theorem from this paper is used as a premise of the new results.
- Alexander Ostrowski, *Über Dirichletsche Reihen und algebraische
  Differentialgleichungen*, Math. Z. 8 (1920), 241–298, inspected in the English
  translation by Erik Christian Hansen, Yonathan Stone and Jesse Wolfson:
  https://arxiv.org/html/2211.02088v1
  The passage immediately before Theorem 11 in Section 5 explicitly attributes
  to Grönwall the unbounded-exponent-ratio criterion for single-series
  differential transcendence. The original Grönwall source was not separately
  inspected.

The user-supplied Wikipedia page was used as orientation, not as a proof
premise. Searches also located general lacunary-series literature; no results
from that literature are imported beyond the clearly identified classical
precedent above.

## What is definitely not claimed new

- Differential transcendence of a single ordinary factorial-gap series.
- Hahn and Conway normal forms, BM differentiation, or the definition of Oz.
- The generic use of lacunarity, polarization, finite-dimensional row rank,
  almost-disjoint families, or the cardinality of a continuum family.
- Cofinite-span invariants as a general idea; the repository already has them.
- Factorial-support algebraic independence and bounded-support descent in the
  repository. The needed special case of descent is included with attribution.
- Existence of differentially transcendental surreal numbers in general.

## Proposed contributions of this manuscript

The jointly presented formulation comprises:

- Complete ordinary and mixed differential relation ideals for arbitrary finite
  families of finite-alphabet rapid-height series, with exact finite-prefix
  corrections and finite-jet transcendence degrees.
- Strongly entire factorial-height functions whose pure z-jets are independent
  over the full scalar Hahn field, although all Taylor coefficients lie in Q(q).
- Arbitrary finite Hermite data within a continuum-sized independent family.
- BM-jet independence of the 0/1 numerical subseries over the bounded-support
  fraction field, via the separately proved jet theorem and known descent idea.
- An exact common strong-evaluation domain in the full surcomplex class.
- Omnific codes with a complete algebraic pattern classification over the stated
  base, and exact factorial floor profiles.

These are proposed additions relative to the inspected sources. There was no
exhaustive MathSciNet, zbMATH, thesis, historical-language or citation-network
search. A mathematically correct theorem can still be a rediscovery. The source
keeps priority uncertainty separate from its written proof claims.

## What remains open in the manuscript

The universal pure-differential rigidity problem for all strongly entire
order-unit Hahn functions; slower-growth height criteria; arbitrary infinite
coefficient alphabets; larger differential bases; intrinsic differential
independence of the scaled omnific codes; infinite interpolation; and formal
verification. No named historical conjecture is reported as solved.
