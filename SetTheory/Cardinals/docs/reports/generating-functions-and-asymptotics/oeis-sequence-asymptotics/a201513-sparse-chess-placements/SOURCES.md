# Sources and scope

Checked 2 October 2026.

## Definitions and previously published leading terms

- OEIS A201513, https://oeis.org/A201513 , ordinary n by n board with n nonattacking kings. Internal record https://oeis.org/A201513/internal lists the leading factorial carrier exp(-9/2)n^(2n)/n!, credited to Vaclav Kotěšovec, 29 November 2011.
- OEIS A201540, https://oeis.org/A201540 , corresponding knight count. Internal record https://oeis.org/A201540/internal gives the same leading term, with the same credit.
- OEIS A201511, https://oeis.org/A201511 , n wazirs, which are orthogonal nearest-neighbor exclusions; leading carrier exp(-5/2)n^(2n)/n!.
- OEIS A201861, https://oeis.org/A201861 , n ferses, which are diagonal nearest-neighbor exclusions; leading carrier exp(-5/2)n^(2n)/n!.

These are unlabeled subsets of board squares, not permutation placements (one per row/column) and not placements modulo board symmetries.

## Kotěšovec book

V. Kotěšovec, *Non-attacking Chess Pieces*, sixth edition, 2013, https://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf . The public file includes later table updates; the edition label does not date all table entries.

The actual PDF was downloaded from the author's HTTP endpoint after the HTTPS endpoint timed out. Relevant pages were text-extracted and the key equation pages visually inspected:

- p. 77: n kings on n by n board, leading equivalent and a preceding fixed-k polynomial expansion
- p. 293: n knights on n by n board, leading equivalent and enumeration table
- pp. 683–684: comparison of fixed-k polynomial coefficients for chess families
- pp. 685–686: general bounded-move leading law, applicable to composite leapers too

The first diagonal corrections and a uniform all-fixed-order moving-k remainder are not displayed on those pages. Fixed-k polynomial data do not alone justify replacing k by n in a remainder. This report establishes the necessary uniform estimate independently. It does not claim the leading equivalent is conjectural or new.

## Existing general analytic methods

Ewan Davies, Matthew Jenssen, and Will Perkins, *A proof of the Upper Matching Conjecture for large graphs*, arXiv:2004.06695, version 2, 29 July 2021: https://arxiv.org/abs/2004.06695 ; PDF https://arxiv.org/pdf/2004.06695 . Section 3 develops the canonical-ensemble independent-set cluster expansion with convergence and tail estimates. Section 1.1 explains the role of small-subgraph counts and credits earlier canonical work by Pulvirenti and Tsagkarogiannis. This source was inspected directly.

Its existence prevents claiming that sparse independent-set asymptotics or the cluster principle themselves are new. The self-contained method here provides a particularly direct finite-support and coefficient-extraction specialization to expanding square boards.

Elena Pulvirenti and Dimitrios Tsagkarogiannis, *Cluster expansion in the canonical ensemble*, Communications in Mathematical Physics 316 (2012), 289–306; https://arxiv.org/abs/1105.1022 . Its abstract and bibliographic record directly confirm a volume-uniform canonical expansion in a low-density regime. This is prior general methodology, not a source for the displayed chess coefficients.

## Search limitation

Targeted searches for the four sequence IDs, nonattacking kings/knights higher-order expansions, and the displayed first coefficients did not locate a previous version of the specialized formulas. The current relevant ProveIt catalog and targeted sequence/name searches did not reveal overlap. These are bounded checks, not a proof of absence from all literature or repositories.
