# Sources, repository provenance, and search scope

## Fixed repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9

The GitHub connector was used to inspect the repository tree, Cardinals/report
README files, and the following relevant package documents:

- https://github.com/VladimirReshetnikov/ProveIt/blob/e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/PROOF_AUDIT.md

These state the uniform-fiber height formula and explicitly exclude a
nonuniform height formula. They identify persistence of a large common
coordinate as an obstruction and give the isolated omega^2 plus two-step
omega-chain example. The new proof is not contingent on the correctness of
other maximal-order-type results in that package.

The neighboring hoare-powerspace-statures README was also inspected to distinguish
its topological stature bounds from this finite nonuniform height problem.
No complete repository build or exhaustive review of every report is asserted.

## Mathematical sources

1. Sergio Abriola, Simon Halfon, Aliaume Lopez, Sylvain Schmitz, Philippe
   Schnoebelen, Isa Vialard, *Measuring well-quasi-ordered finitary powersets*,
   arXiv:2312.14587v2 (2024).
   https://arxiv.org/html/2312.14587v2
   Used for definitions, WPO closure, and the wider extension program in Section 6.
   The concluding page was visually inspected. The present article does not
   assert that the whole program is solved.

2. Elliott Samuel Wolk, *Partially well ordered sets and partial ordinals*,
   Fundamenta Mathematicae 60(2) (1967), 175–186.
   DOI: 10.4064/fm-60-2-175-186.
   The primary journal index confirms bibliographic metadata:
   https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/60/2
   Theorem 9's modern statement and attribution were checked in the next source;
   direct full-text retrieval of Wolk through EuDML was unsuccessful.

3. Alberto Marcone, Antonio Montalbán, Richard A. Shore, *Computing maximal
   chains*, arXiv:1201.4408 (2012).
   https://arxiv.org/abs/1201.4408
   Author-hosted text:
   https://richardashore.github.io/papers/pdf/MC0116x12.pdf
   Theorem 1.2 states Wolk's strongly maximal-chain theorem. The first two pages
   were visually inspected. This provides the classical height-attainment input.
   Its uniform computability results are not contradicted by our finite schedule
   algorithm, which requires supplied component heights and component chains.

4. Isa Vialard, *On maximal order type of the lexicographic product*, Logic
   Journal of the IGPL 33(4) (2025), jzaf051.
   https://doi.org/10.1093/jigpal/jzaf051
   Publisher metadata was checked. This is neighboring work on a different
   invariant; no theorem from it is used in the proof.

5. Jean Goubault-Larrecq and Bastien Laboureix, *Statures and Sobrification
   Ranks of Noetherian Spaces*, arXiv:2112.06828.
   https://arxiv.org/pdf/2112.06828
   Consulted for the distinction between rank and chain length in general
   well-founded orders. No result from this source is a required premise beyond
   the independently stated classical inputs above.

## Novelty-search limits

Queries included the exact titles above, “finitary powersets height lexicographic”,
“lexicographic sums height powersets”, and maximal-chain results for WPOs.
The exact nonuniform retirement-weight formula was not identified in the checked
sources. This is not an exhaustive literature review and does not certify
priority. The supported research claim is a proved extension of the explicitly
stated scope of the inspected repository package.

External PDFs, repository PDFs, and font files are not redistributed. The
package contains only the newly generated article, code, data, and documentation.
