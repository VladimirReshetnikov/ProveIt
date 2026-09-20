# Sources and comparison record

Retrieval date: September 20, 2026.

## OEIS A195806

https://oeis.org/A195806

The entry defines the triangular side-five arrays with entries 0..n, zero corners,
and equal sums on rows/diagonals of the same length. The entry was introduced by
R. H. Hardin on September 23, 2011. Its offset is 1, and its first term is 16.
The displayed formulas, attributed to Manuel Kauers and Christoph Koutschan on
March 1, 2023, were still headed "Conjectured recurrence" and "Conjectured closed
form as a quasi-polynomial" at retrieval.

The manuscript's table agrees with these six formulas, with the last residue
expanded. Its order-14 constant-coefficient recurrence agrees with the displayed
OEIS recurrence. A(0)=1 is the natural extension used in the manuscript.

## Published paper

Manuel Kauers and Christoph Koutschan, *Some D-Finite and Some Possibly D-Finite
Sequences in the OEIS*, Journal of Integer Sequences 26 (2023), Article 23.4.5.

Journal landing page:
https://cs.uwaterloo.ca/journals/JIS/VOL26/Koutschan/kout4.html

Journal PDF:
https://cs.uwaterloo.ca/journals/JIS/VOL26/Koutschan/kout4.pdf

arXiv record:
https://arxiv.org/abs/2303.02793

arXiv PDF:
https://arxiv.org/pdf/2303.02793

Relevant material: Section 5.1, printed pages 24–25; Figure 3, the defining linear
system, and Conjecture 11 on printed page 25 (PDF page index 24). The paper already
establishes quasipolynomiality and D-finiteness, while leaving the explicit formula
conjectural. The journal and arXiv page images were checked for the displayed array
and formula; the audit does not rely on OCR.

## Exact correction

Let T(n) be the printed expression in Conjecture 11. Its final constant is 19496
in both PDFs inspected. The proof and exact polynomial comparison establish:

    T(n) = A(n+1)                 when n is not 5 modulo 6;
    T(n) = A(n+1) + 1/48         when n is 5 modulo 6.

Replacing 19496 by 19469 gives A(n+1) for every nonnegative n. At n=5 the printed
expression equals 598513/48, whereas A(6)=12469.

This is a one-step indexing difference and an additional numerical typo. The
mathematical result in the manuscript is the full derivation of the correctly
indexed OEIS formulas from the array conditions, not merely the observation that
a misprinted rational value cannot be a count.

## Scope of the literature check

Searches used the sequence identifier and proof-related terms, in addition to
checking the OEIS entry and the paper. No later proof was located in the inspected
results. This does not prove that no earlier resolution exists or establish
priority for the derivation and extensions supplied here. No claim is made that
every conjecture in the 2023 paper is still open.
