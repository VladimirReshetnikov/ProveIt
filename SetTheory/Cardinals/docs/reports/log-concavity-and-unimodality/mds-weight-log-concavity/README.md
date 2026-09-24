# A First-Triple Criterion for Log-Concavity of MDS Weight Distributions

Research article and reproducibility package, 20 September 2026.
Prepared for Vladimir Reshetnikov.

## Result

For integer parameters d = n-k+1 >= 2, k >= 3, and q > d, the
compressed formal MDS weight distribution (1, A_d, ..., A_n) is
log-concave if and only if A_(d+1)^2 >= A_d A_(d+2). Equivalently,

    P(q) = (n+1)q^2 - Bq + dB/2 >= 0,
    B = k(d^2+2d-1)+2.

There is no restriction on dimension relative to length, nor on length
relative to alphabet size. Every other internal inequality is strict
when this criterion holds. The article supplies a self-contained proof
using alternating negative-binomial partial sums and the bound

    D_s/E_s <= (s / 2^(s-1)) (D_1/E_1),  for odd internal offsets s.

It also proves the q=d boundary classification, exact length thresholds
for single-parity-check codes, a fixed-distance dimension cutoff, a
uniform alphabet threshold, and a fixed-positive-rate asymptotic.

Zero coefficients are deleted; the weight-zero coefficient A_0=1 is
retained. Formal parameter arrays are not constructions of codes, and
none of the formal computations establishes code existence. In
particular, this work does not solve the MDS existence conjecture.

## Research target and status

A single OS-random draw selected coding theory as index 16 of 24 areas.
The ordered list and actual result are in data/random_selection.json.

The target is the high-dimension extension discussed in Remark 2 of:

Minjia Shi, Xuan Wang, Junmin An, and Jon-Lark Kim,
*Log-Concave Sequences in Coding Theory*, arXiv:2410.04412v1 (2024),
Section 5, Theorem 9 and Remark 2.
https://arxiv.org/abs/2410.04412

The accessible preprint establishes the quadratic criterion in its
positive-weight regime under k <= n/2+3. This article removes that
restriction for q>d and treats the zero-coefficient boundary separately.
The 2025 IEEE journal record's indexed abstract retains the dimension
restriction. Searches made on 20 September 2026 found no subsequent
removal. The full journal PDF was not retrieved. See
`data/literature_audit.json` for the precise scope and access limitations.

This is a conventional mathematical proof with executed exact checks,
not a proof-assistant formalization or an independently peer-reviewed
result. The literature search is not a certification of priority.

## Reading and rebuilding

Read `article.pdf`. The complete editable source is `article.tex`;
its numerical table is embedded, so the article has no external figure
or table dependencies.

With a standard TeX installation and latexmk:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Without latexmk, run this command until cross-references stabilize
(typically three times from a clean directory):

    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The preamble lists the required standard packages. No bibliography tool
is needed; references are included in article.tex.

## Exact verification

Python 3.9 or later; no third-party packages:

    python code/verify.py --max-n 200 --output data/verification.json
    python code/mds.py 11 9 11
    python code/mds.py 16 15 5
    python code/mds.py 6 3 4

The first command regenerates the full verification record. It took
approximately 21 seconds in the authoring environment. The other
commands report the formal distributions, theorem predictions, and
directly detected inequalities for individual examples.

The distributed record reports all checks passing:

| Check | Count |
| --- | ---: |
| Main-case formal parameter triples, q>d | 154,888 |
| Formal boundary triples, q=d>=3 | 15,642 |
| Binary boundary lengths | 499 |
| Degenerate-case parameter checks | 1,633 |
| Independent inclusion-exclusion comparisons | 1,815 |
| Exact rational checks of the key defect bound | 45,066 |
| Explicitly enumerated actual small codes | 64 |
| Codewords enumerated across those codes | 20,798 |

Main-sweep digest:

    a1ee90c8c03cd271a580b3bba2857dc03bc846d656b84dee592796f8d8d44351

This digest covers the deterministic ordered parameter/decision record,
not timing or other environment metadata. Finite checks corroborate the
proof; the proof, not the sweep, establishes the universal statement.
`--max-n` controls only the main sweep; the other checks retain their
documented fixed ranges.

To regenerate the threshold table:

    python code/make_tables.py

This rewrites the two threshold-data files and the marked table block
inside article.tex. Prime-power selection and threshold comparisons
use exact integers. Decimal approximations are used only for display.

## Contents

- `article.tex`, `article.pdf`: article, including complete proofs and references.
- `code/mds.py`: formal enumerator and full conditional classification.
- `code/verify.py`: exact formal-array and constructed-code checks.
- `code/make_tables.py`: reproducible threshold table generation.
- `data/verification.json`: executed counts, examples, constructed-code list, digest.
- `data/random_selection.json`: original area-selection record.
- `data/thresholds.csv`, `data/threshold_rows.tex`: threshold data and table rows.
- `data/literature_audit.json`: research target, sources, and search limitations.
- `Makefile`: optional build/check convenience targets.

External source articles, font files, and intermediate TeX build products
are not included.
