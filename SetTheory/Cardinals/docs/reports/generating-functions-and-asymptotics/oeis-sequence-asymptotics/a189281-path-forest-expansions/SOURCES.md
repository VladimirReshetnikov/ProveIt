# Source and novelty audit

Sources inspected on 1 October 2026. The article contains inline bibliographic
citations; this file records the scope of the review, not a proof of priority.

## OEIS targets

- A189281: https://oeis.org/A189281/internal
  The entry states the signed difference-two restriction, identifies its
  specific recurrence as conjectural, and describes the higher expansion as
  an implication of that recurrence. The exact n=0,...,21 values used for the
  independent enumeration check are in its displayed sequence.
- A110128: https://oeis.org/A110128/internal
  The entry states the absolute difference-two restriction, links a guessed
  order-24, degree-64 operator, and attributes the higher expansion to it.
  The displayed n=0,...,21 values are used for the same check.

## Mathematical antecedents

- George Spahn and Doron Zeilberger, *Counting Permutations Where The Difference
  Between Entries Located r Places Apart Can never be s*, 2022, revised with
  postscript:
  https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimPDF/permsV2.pdf
  Exact matching-of-tilings inclusion-exclusion is inherited and credited.
- Roberto Tauraso, *The Dinner Table Problem: The Rectangular Case*, Integers 6
  (2006), A11:
  https://arxiv.org/abs/math/0507293
  Prior exact formulas and the diagonal absolute-case leading correction.
- Manuel Kauers and Christoph Koutschan, *Guessing with Little Data*, ISSAC 2022,
  pp. 83–90:
  https://arxiv.org/abs/2202.07966
  Recurrence-guessing context; no guessed operator is assumed in this report.
- Jaideep Sai Padhi, *Solutions to Five Challenge Problems in Enumerative and
  Algorithmic Combinatorics, with an Account of the Human–Machine Methodology
  Employed*, arXiv:2608.11290, August 2026:
  https://arxiv.org/pdf/2608.11290
  Sections 5–6 report general holonomicity and partial progress on the specific
  A189281 operator. This report does not independently validate or use that
  holonomicity proof. The broader manuscript's other results are outside scope.
- NIST DLMF, gamma asymptotics and Lambert W:
  https://dlmf.nist.gov/5.11
  https://dlmf.nist.gov/4.13
  Standard analytic inputs to index inversion.

## Repository context

https://github.com/VladimirReshetnikov/ProveIt

The repository was inspected through its GitHub connector. Targeted searches
included A189281 and asymptotics; these are not an exhaustive audit of every
file. The file read for asymptotic-proof status conventions was
`Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`.
Its contents are project context, not a dependency of the present theorem.
No repository file was changed, and no new Lean build was run.

## Result boundaries

The report's main proof is independent of specific recurrence conjectures.
It establishes the coefficients and controlled all-orders remainder directly
from the underlying counting problem. The leading Poisson behavior, exact
inclusion-exclusion framework, and previously displayed numerical coefficients
are not presented as new discoveries.

The new-to-this-investigation contribution is the exact stable-forest formula
and its use in a uniform all-orders theorem, denominator control, whole-law
universality, and rigorous inversion. A comprehensive historical novelty
claim would require further specialist review. A missing proof in an OEIS
entry alone is not evidence that no proof exists elsewhere.

Section 11's stronger rational collapse is intentionally unproved. Its finite
symbolic checks and the conditional integrality implication must not be cited
as an unconditional integrality theorem.
