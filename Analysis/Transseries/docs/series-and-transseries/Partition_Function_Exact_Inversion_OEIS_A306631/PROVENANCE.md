# Source and claim audit

Report date and source-check date: 3 October 2026.

## Primary mathematical input

Fredrik Johansson, *Efficient implementation of the Hardy–Ramanujan–Rademacher
formula*, LMS Journal of Computation and Mathematics 15 (2012), 341–359.

- https://arxiv.org/abs/1205.5991v2
- https://arxiv.org/pdf/1205.5991
- https://doi.org/10.1112/S1461157012001088

Rademacher's convergent identity is the quoted theorem. The PDF formula was
visually checked. The elementary tail bound used by this report is derived
in the report rather than taken from an unrecorded effective-error theorem.

## OEIS target and related sequences

- https://oeis.org/A306631/internal
  The inspected entry defines the rounded negative-branch Lambert inverse
  and explicitly labels a(p(n))=n for n>9 as a conjecture. It credits
  Jean-François Alcover and dates the sequence to 2 March 2019.
  Its displayed entry revision was #16, 16 February 2025. The site-wide
  footer date is not the entry's revision date.
- https://oeis.org/A000041
  Ordinary partition numbers.
- https://oeis.org/A050811/internal
  Rounded forward Hardy–Ramanujan approximation. Its leading forward-error
  formula is already recorded there and is not claimed as new in the report.

## Forward-asymptotic literature context

Koustav Banerjee, Peter Paule, Cristian-Silviu Radu and Carsten Schneider,
*Error bounds for the asymptotic expansion of the partition function* (2022).
https://arxiv.org/abs/2209.07887

This is cited to acknowledge existing effective forward expansions; it is
not an unstated input to the n>=400 argument.

## ProveIt context

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot obtained from the repository tree:
`d68b65ea064084fb121df9bb431b21d086f7be81`.

The following article's opening 160 lines were inspected at that snapshot:

https://github.com/VladimirReshetnikov/ProveIt/blob/d68b65ea064084fb121df9bb431b21d086f7be81/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a292507-binomial-partition-transform/article.tex

It is a report on all-orders asymptotics, inverse residuals and integer
thresholds for A292507, with explicit unrefereed/non-formalized status notes.
It supplies methodological context, not a theorem assumed by this report.
No claim is made that every repository document was inspected. A targeted
repository search for A306631 returned no matching content. The search
index and a fetched current snapshot can differ, so this negative result
is not treated as a definitive repository-wide absence statement.

## Status of the results

The article supplies proofs of the specific exact rounding classification,
sharp inverse-bias bounds, and derived calibration and inversion results.
It also gives convergent analytic expansions and fixed finite-sector
arithmetic corrections, with the limitations stated in their theorems.

The report is not peer reviewed and not formalized in Lean or Rocq. The finite
certificate is exact rational arithmetic executed in Python. The analytic
infinite-range proof is in the article, not verified by that Python program.
The numerical experiment file is not a rigorous certificate.

The limited literature search did not identify a prior proof of the exact
A306631 statement. No comprehensive publication-priority claim is made.
Classical Rademacher theory, Lambert inversion and existing forward partition
asymptotics are credited rather than presented as new discoveries.

No GitHub repository changes and no OEIS submissions were made.
