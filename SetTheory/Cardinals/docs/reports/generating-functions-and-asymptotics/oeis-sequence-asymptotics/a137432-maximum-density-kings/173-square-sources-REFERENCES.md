# Primary sources and provenance

Inspected 3 October 2026 unless noted otherwise.

1. OEIS A137432, https://oeis.org/A137432
   Exact cylindrical count, offset 0, ratio conjecture, and the leading equivalent
   credited to Václav Kotěšovec on 29 July 2023, updated 18 March 2024.
2. Rintaro Matsuo, Polynomial-time algorithm for the calculation of OEIS A137432,
   https://github.com/windows-server-2003/OEIS_calculation/tree/master/contents/A137432
   Prior binary-word/cyclic-height encoding and O(n^4) multiprecision-operation
   algorithm. The companion reimplements small checks independently.
3. Matsuo's published term table,
   https://raw.githubusercontent.com/windows-server-2003/OEIS_calculation/master/contents/A137432/b137432.txt
   The selected factual fixture records the retrieved upstream SHA-256, URL and date.
   The large terms used for residuals are published inputs, not freshly recomputed.
4. Václav Kotěšovec, Non-attacking Chess Pieces, sixth edition (2013), pp. 209–210,
   http://www.kotesovec.cz/books/kotesovec_non_attacking_chess_pieces_2013_6ed.pdf
   The relevant pages were rendered and independently inspected. The strict upper
   bound a_n < 2^n(n+1)^n must exclude n=1, where equality holds.
5. Michael Larsen, The Problem of Kings, Electronic Journal of Combinatorics 2
   (1995), R18, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v2i1r18/pdf/
   Concerns the ordinary planar board, not the horizontal cylinder.
6. Tricia Muldoon Brown, Maximum arrangements of nonattacking kings on the 2n × 2n
   chessboard, Recreational Mathematics Magazine (2025), pp. 41–52,
   https://doi.org/10.2478/rmm-2025-0003
   Also the ordinary planar board.
7. Eli Bagno, Estrella Eisenberg, Shulamit Reches, Moriah Sigron, Counting King
   Permutations on the Cylinder, https://arxiv.org/abs/2001.02948
   Counts permutation configurations with one king in each row and column.

The report's geometry, transfer identity, caterpillar representation, uniform
expansion, first coefficients, total-variation and moment rates, and integer
inverse bracket received an independent mathematical audit. Exact-count tests,
coefficient computations and residuals were independently regenerated. The current
package adds isolated normal/-O checks and an extracted rebuild.

An earlier overlap search was not independently reproduced and supplies no
exhaustive-priority evidence. The inspected primary materials do not display the
correction expansion proved in the report. This is a bounded comparison, not a
first-in-history claim. No full third-party book, paper or downloaded source
implementation is distributed.
