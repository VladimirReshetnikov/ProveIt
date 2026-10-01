# Source and novelty audit

Date: 30 September 2026.

## Repository pin and inspected material

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `0744012ba29db0e345c44be953c6de3e000439e6`

Report path:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/`

Main article blob: `1b7f9ed9d7831b88ac999fc1d665d14caabf6481`

Pinned article:
https://github.com/VladimirReshetnikov/ProveIt/blob/0744012ba29db0e345c44be953c6de3e000439e6/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/article.tex

Pinned README:
https://github.com/VladimirReshetnikov/ProveIt/blob/0744012ba29db0e345c44be953c6de3e000439e6/SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/README.md

The GitHub connector was used for repository reads. The report's README, status
record, relevant article sections, and related search results were inspected.
The original 147-page report was not audited line by line in its entirety.

Relevant source locations:

- Section 41.4: finite exponential expansion, explicit residue annihilator,
  and rationality. Its theorem expressly does not assert general minimality.
- Question 44.15, label `evo:q:recurrence`: minimal recurrences, cancellation
  of bases, and closed numerators including the finite initial correction.
- Section 55: the minimal four-output full polynomial of degree 15, and the
  later remark establishing residue minimality at four outputs.
- Parts II-III and README: exact three-output formula, eventual formula for
  k>=4 with explicit threshold <=3 k^4, and the all-n slices for k=4,...,7.
- README status: AI-assisted, unrefereed; no proof-assistant formalization.

The present manuscript does not claim a counterexample to an asserted minimality
theorem: the source anticipated that some factors might be unnecessary. It gives
exact selection tests and an explicit genuine cancellation. The four-output
polynomial is prior repository work, reproduced only as a consistency check.

## Primary external sources

1. Sylvie Davies, *State Complexity of Reversals of Deterministic Finite Automata
   with Output*, arXiv:1705.07150v2, 17 October 2017.
   https://arxiv.org/html/1705.07150v2
   Read the definitions, reverse coloring automaton, orbit characterization,
   and descriptions of binary lower bounds/questions. The orbit characterization
   is cited and its short accessibility argument is recalled in the article.

2. Kevin Ford, *Integers with a divisor in (y,2y]*, arXiv:math/0607473.
   https://arxiv.org/pdf/math/0607473
   The first PDF page was read both as extracted text and as a screenshot.
   It states the multiplication-table estimate and the exponent
   1-(1+log log 2)/log 2. The current PDF displays version v5 and an internal
   November 26, 2024 date; neither date is used as a mathematical premise.

3. Kevin Ford, *The distribution of integers with a divisor in a given interval*,
   Annals of Mathematics 168 (2008), 367-433.
   https://annals.math.princeton.edu/2008/168-2/p01
   DOI: 10.4007/annals.2008.168.367.
   Publisher metadata and abstract checked. The exact multiplication-table
   formula is taken from source 2, not inferred from this abstract.

4. James L. Massey, *Shift-register synthesis and BCH decoding*, IEEE Transactions
   on Information Theory 15 (1969), 122-127. DOI: 10.1109/TIT.1969.1054260.
   Author's publication archive:
   https://www.isiweb.ee.ethz.ch/archive/massey_pub/dir/pdf.html
   Bibliographic details checked there. The classical algorithm is used as a
   finite cross-check; the article's universal minimality proofs do not depend
   on trusting its implementation.

## Novelty boundary

The targeted searches included DFAO reversal, minimal recurrences, spectral
cancellation, and nineteen-output coloring terms. Relevant search hits included
Davies's paper; they did not yield an external result matching the exact
nineteen-output certificate or the complete three-moment factor tests. Search
results were often sparse or irrelevant. There was no exhaustive citation-index
review, survey of theses, or correspondence with authors. Therefore absence of a
matching hit is not proof of priority.

The article's priority claim is restricted to a concrete continuation relative to
the pinned ProveIt material inspected. Classical palette counting, Fourier
analysis on four residues, exponential-polynomial independence, and the
multiplication-table theorem are attributed or reproved, not presented as new
methods. New claims are the explicit factor-selection formulas and their stated
applications, within the proof/dependency boundaries in PROOF_STATUS.md.
