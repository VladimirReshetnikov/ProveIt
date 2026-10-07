# Source ledger

Retrieved and checked 5 October 2026. Hashes below identify the retrieved source bytes, not a guarantee that an online page never changes. The original third-party PDFs and HTML snapshots are not redistributed in this package. The three included OEIS b-files retain the retrieved bytes.

## Primary mathematical sources

Peter J. Cameron, Thomas Prellberg and Dudley Stark, Asymptotic enumeration of 2-covers and line graphs, Discrete Mathematics 310 (2010), no. 2, 230–240. DOI: https://doi.org/10.1016/j.disc.2008.09.008

Corrected author manuscript, 20 pages:
https://maths.qmul.ac.uk/~pjc/preprints/cover.pdf
Alternate working author URL:
https://webspace.maths.qmul.ac.uk/p.j.cameron/preprints/cover.pdf
Retrieved bytes: 196940
SHA-256: 9bdc218b4f82853ebf71a939dbbfb32a0abaa5b197de80d184f20f5e10eac164

Key locators: Proposition 1 pp.3–4 for graph dictionary; Proposition 3 p.5 for U=e^x V; corrected Proposition 5 p.6 for the four line-graph corrections; equation (18) p.16 for V=e^(-x/2)H; equations (21)–(27) pp.17–18 and discussion p.19 for the leading equivalent; p.19 explicitly prints the corrected L multiplier and acknowledges the referee's correction.

Original arXiv version, 19 pages, 4 July 2007:
https://arxiv.org/pdf/0707.0664v1
Retrieved bytes: 175905
SHA-256: f81d26c62600cdcc072e271beeaf820cc152b5b7cae5e176409e537949a13a21

Its Proposition 5 p.6 has the obsolete cubic-only correction. The corrected author manuscript, not this earlier formula, determines L in this report. The typeset journal PDF was not independently retrieved.

NIST DLMF https://dlmf.nist.gov/4.13 and https://dlmf.nist.gov/5.11 provide standard Lambert-W conventions and finite positive-real Stirling expansions. No infinite Stirling series is assumed to converge.

## Numerical entry snapshots

A060053: https://oeis.org/A060053
Included b-file: https://oeis.org/A060053/b060053.txt
Index range 0..100; 11080 bytes
SHA-256: 839ce91b32fedfef2f6135669dd3a7c1c547f4eafe5b68678b8a4cd51ac08b8d

A014500: https://oeis.org/A014500
Included b-file: https://oeis.org/A014500/b014500.txt
Index range 0..100; 11121 bytes
SHA-256: 0f29a6a73d98dd48e5c2240bc88d9d95b153d341fbe1d65dbdbbac19991ebcd9

A132219: https://oeis.org/A132219
Included b-file: https://oeis.org/A132219/b132219.txt
Index range 1..18; 302 bytes
SHA-256: 8f6a66e313320dedfff9b903a366067d86f237145ca57651582c86ce2c546457

The A132219 terms all agree with exp(-x^3/6)U(x), whereas corrected L=exp(-x^3/6-x^4/4-x^5/8-x^6/48)U. First discrepancy: n=4, legacy 66 versus corrected 60.

A060053 revision 51 and A014500 revision 52 were current in the retrieved histories, both dated 30 May 2026. The current entries and all retained revision diffs (1–51 and 1–52, with no gaps) were inspected. No asymptotic coefficient conjecture or O(n^-3) remainder claim was found there. Accordingly the report does not attribute its higher-order formulas, or the need for logarithmic remainder factors, to an OEIS conjecture.

## Coverage limits and attribution

The exact identities, exception classification and leading equivalent are prior CPS results. Small endpoint enumeration independently validates the consequences through six edges; it does not prove completeness of the structural exception theorem. The report supplies its own saddle, coefficient and inverse arguments. Source coverage is not an exhaustive historical search and does not establish worldwide novelty.
