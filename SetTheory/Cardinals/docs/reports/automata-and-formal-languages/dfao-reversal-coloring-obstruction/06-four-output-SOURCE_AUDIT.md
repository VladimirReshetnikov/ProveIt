# Source and novelty audit

Date of inspection: 29 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `c130dba623c420551d90db41dae7b3d9cff72dfd`.

The task was scoped after reading the repository overview and research-report
manifest. The specific predecessor is:

```text
SetTheory/Cardinals/docs/reports/automata-and-formal-languages/
dfao-reversal-coloring-obstruction/
```

The README, full article source, and `code/reversal.py` were inspected through
the connected GitHub reader. The live repository may have changed afterward;
all comparisons in this package are to the pinned snapshot.

Pinned article:
https://github.com/VladimirReshetnikov/ProveIt/blob/c130dba623c420551d90db41dae7b3d9cff72dfd/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/article.tex

Pinned README:
https://github.com/VladimirReshetnikov/ProveIt/blob/c130dba623c420551d90db41dae7b3d9cff72dfd/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/README.md

## Boundary against the predecessor

Already present in the inspected predecessor: the coloring-orbit reduction;
the collision graph method and its graph classification; a universal
structural upper bound; finite equality with Davies's lower construction
for `7 <= n <= 30, 3 <= k < n`; and the all-state three-output result,
including three-output rigidity and related consequences.

Explicitly left open there: the exact result for `k >= 4` outside its finite
range. Part II's Question 23.1 and the README's “Not claimed” section record
that limitation.

Contribution relative to that snapshot: an all-state four-output upper bound,
a strict comparison selecting the nearest coprime split, four-output
rigidity, the stated four-color second-collision penalty, secondary-scale
stability, and the derived four-output orbit inventory and exact asymptotics.

No claim is made that graph coloring, the orbit reduction, primitive-word
counting, the biclique chromatic polynomial, or the lower-bound witness is
new. The elementary needed statements are reproved in the manuscript. The
old three-output proof is not used as an admitted premise.

## Primary external literature

1. Sylvie Davies, *State Complexity of Reversals of Deterministic Finite
   Automata with Output*, arXiv:1705.07150v2, 17 October 2017.
   https://arxiv.org/abs/1705.07150
   https://arxiv.org/pdf/1705.07150v2

   Inspected: full parsed article; displayed open-question page. Relevant
   printed pages: 5–6, Propositions 3–4; 7, the definition of `U_(a,b)` and
   explicit parity-adjusted generators; 9, Theorem 3; 12, Corollary 3;
   17, Problem 2 and the small-value table.

   The source already supplies the lower bound used for attainment. We do
   not claim its generator, orbit interpretation, or small lower-bound
   numbers as new. Our theorem proves the matching upper bound for four
   outputs for all `n >= 7`.

2. Markus Holzer and Barbara König, *On deterministic finite automata and
   syntactic monoid size*, Theoretical Computer Science 327(3) (2004),
   319–347. DOI: 10.1016/j.tcs.2004.04.010.
   https://www.sciencedirect.com/science/article/pii/S0304397504004840

   The official publisher metadata was checked. The precise two-generator
   input is Theorem 8 as stated and applied in Davies's article, printed
   page 7. This package does not claim an independent reconstruction or
   machine verification of the full Holzer–König proof. The explicit maps
   are taken from Davies's recorded generating set.

   The larger question of maximum size of an arbitrary two-generated
   transformation monoid is not assumed or resolved here.

## Targeted searches and limitations

Queries included the full Davies title; “DFAO reversal four”; and
combinations of “Davies”, “reversal”, “optimal”, and “output”. A connected
GitHub code search for “four-output” in ProveIt returned one unrelated
Hilbert-tenth-problem file and no relevant reversal continuation. The pinned
report's own explicit scope was the main repository-level evidence.

No later resolution was identified in these targeted checks. This is not an
exhaustive scholarly citation-index search, a review of every thesis or
unindexed manuscript, or correspondence with the authors. It does not
establish priority or guarantee that the proposed results are new to the
literature. The article is an unrefereed research contribution with an
explicit proof and reproducible finite certificate.
