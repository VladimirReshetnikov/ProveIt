# Source, novelty, and verification audit

## Repository basis

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `cd80e5e0adc2a1a25e8cc64d52abc8acb093d801`.

The branch record gives 2026-09-23 04:19:30 UTC, which is 2026-09-22 in Pacific time. The article uses the latter calendar date.

Read through the connected GitHub interface:

- Root directory metadata and the relevant part of `README.md`.
- The documentation directory tree and `docs/README.md`, to identify nearby research and its review boundaries.
- `docs/NORMAL_FORM_BRIDGE.md`, lines 1–165 at the pinned revision, to identify actual small-support normal-form, evaluation, cut, valuation, and strong-sum infrastructure.
- The main-branch revision record, to pin the inspected snapshot.

The new mathematical proofs do not rely on an unreviewed repository conjecture. They import classical normal forms, Hahn operations, and the surreal small-cut property. The repository discussion identifies possible formalization interfaces rather than claiming that this article's theorems have already been checked there.

The inspection is not an exhaustive search of every source file, historical branch, manuscript, and proof in the repository. No repository write was made. No Lean build of this article's results was run.

## Prior project manuscript

The user's research Library supplied `omnific_integers_diophantine.tex`, titled *Omnific Integers and Diophantine Geometry: Arithmetic Retractions, Rigidity, and Infinite Families*, dated 22 September 2026.

Its retrieved passages establish provenance for the earlier constant-term retraction, finite quotient/completion discussion, set-sized denominator clearing, and common positive support shift. Those ingredients are not claimed as new here. All support-shift arguments needed in the present article are proved again, so access to that separate draft is not required to follow the new proof.

The prior manuscript is not assumed to be peer reviewed, completely formalized, or present in the pinned GitHub tree. It has not been redistributed in this archive.

## Published and classical sources

1. John H. Conway, *On Numbers and Games*, 1976; second edition 2001. Classical background for surreal arithmetic and normal forms.
2. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, Cambridge University Press, 1986, LMS Lecture Note Series 110. DOI: https://doi.org/10.1017/CBO9780511629143 . The publisher's indexed catalogue was used for bibliographic checking.
3. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised power series and omnific integers*, Advances in Mathematics, article 109513 (2024). DOI: https://doi.org/10.1016/j.aim.2024.109513 . Inspected version: https://arxiv.org/html/1710.07304v5 and its arXiv metadata.

The L'Innocente–Mantova text is especially important. Remark 3.4.4 gives a countable geometric-series product with a monomial result in a non-Archimedean exponent group. That mechanism is a direct precursor, not something newly discovered in this article. Its adaptation to pairwise differences with a fixed common multiple is fully proved here; the proposed contribution is the resulting arbitrary-set-target and support-threshold theorems.

The article's largest-growth-exponent function is distinct from the ordinal support-degree functions considered in the factorization paper. The notation and distinction are made explicit.

## Novelty boundary

The search included combinations of “omnific integers”, “set-sized”, “homomorphism”, “quotient”, “purely infinite ideal”, and the names of the relevant published factorization results, alongside the project catalogue and prior omnific manuscript.

No exact published precedent for Theorems 5.1, 7.2, and 11.1 was identified in this bounded comparison. That is not a certified absence result. Sparse or irrelevant search results do not establish priority. The manuscript labels these as proposed contributions, supplies proofs, and makes no claim to have solved a named longstanding published conjecture.

The associated quotient, module, derivation, and localization statements are treated as connected deductions rather than as independent priority claims.

## Mathematical checks emphasized in the article

- Every individual normal-form support is a set.
- Every cardinal contradiction is applied to a set-indexed family larger than the target, not to a fictitious cardinality of the proper class of all surreals.
- The telescoping support is strictly decreasing and strictly positive, so it defines an admissible countable normal form.
- The infinite identity is proved by coefficient cancellation, not by dropping the nonzero remainder of a finite truncation.
- Arbitrary homomorphisms are applied only to finite ring identities; they are not assumed to preserve Hahn sums.
- A common positive support shift handles every purely infinite element, not just finite sums of monomials.
- The finite-side quotient lies in the infinitesimal ideal by valuation; its support cardinality is separately checked for the bounded-support theorem.
- The countable-support theorem keeps the exponent class equal to the full surreal class. Fixed set-sized Hahn fields are explicitly excluded from that collapse statement.
- The target endomorphism ring of a set-sized module is itself a set, even if it is noncommutative.
- Quotient statements use set-realizable kernels; no set of class cosets is silently presumed.

## Computational and document verification

`verify_identities.py` uses exact `fractions.Fraction` coefficients and lexicographic pairs of rational exponents. The deterministic report records:

- 1,950 finite telescoping identities, with positive supports and nonzero remainders retained.
- 600 same-sign constant-coefficient multiplication identities.
- 900 finite-augmentation multiplication identities.
- Three rank-one support-failure examples and three explicit distinguishing examples.

These checks do not constitute infinite-series or set-theoretic verification. The complete mathematical arguments are in the article. No Lean code is included because no kernel check of the proposed results was performed.

The final PDF was compiled from the delivered source, rendered for visual inspection, and checked for layout warnings and text outside its expected page area. The concrete build and package results are recorded in `build_report.json`.
