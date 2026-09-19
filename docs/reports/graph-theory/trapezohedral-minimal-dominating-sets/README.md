# A marked-cycle proof of the trapezohedral domination conjecture

**Research manuscript, 19 September 2026 — OEIS A381190**

Read `article.pdf`; its complete, self-contained LaTeX source is `article.tex`.
The manuscript proves the generating function still labeled conjectural in
the inspected OEIS record and derives additional enumeration and limit laws.
The mathematical proof is complete as presented. Literature priority has not
been independently established; the work is not peer-reviewed or formalized
in a proof assistant.

## Main result

For the n-trapezohedral graph (n >= 3), let a_n count dominating vertex subsets
that are inclusion-minimal among **all dominating sets** and induce a connected
subgraph. This is not the different notion “minimal connected dominating set.”

Let p_0=1, p_1=0, p_2=1 and p_m=p_(m-2)+p_(m-3). Then

    a_n = 2*n*(2*p_(n-2) + p_(n-3)).

Equivalently, using the OEIS indexing of A000931,

    a_n = 2*n*(2*A000931(n+1) + A000931(n)).

The proof classifies the sets by a cyclic arrangement of gaps of lengths 2
and 3, with a restricted marked edge. It handles n=3 explicitly. Consequences
include an exact size/type distribution, strict log-concavity, an unbiased
sampler, a Binet formula, exact nearest-integer evaluation for n>=4, and a
central limit theorem for size.

## Contents

- `article.tex`, `article.pdf`: the 20-page manuscript, including full proofs,
  three TikZ diagrams, source attribution, and reproduction instructions.
- `code/research.py`: standard-library exact counts, size distributions,
  structural generation, graph-based tests, and uniform sampling.
- `code/exhaustive.cpp`: independent, portable C++17 all-subsets enumeration.
- `code/verify_symbolic.py`: optional SymPy/mpmath symbolic and numerical audit.
- `data/counts.csv`: totals, normalized totals, and topology counts, n=3..1000.
- `data/b381190.txt`: the same total sequence in OEIS b-file style.
- `data/size_distribution.csv`: counts by size and topology, n=3..100.
- `data/exhaustive.csv`: every accepted vertex mask for n=3..11.
- `verification/`: recorded exact tests, symbolic tests, environment, source
  audit, and PDF-build/inspection summary.
- `oeis_update.txt`: a suggested formula and compact proof note, not submitted.
- `requirements-optional.txt`: dependencies only for the optional audit.
- `Makefile`: convenience targets on systems with make, g++, Python, and TeX.
- `MANIFEST.sha256`: file-integrity checksums.

All generated counts are computed from the proof, not downloaded from an OEIS
b-file. The 40 published initial values are separately embedded as comparison
fixtures with source attribution in the manuscript and source audit.

## Run the standard-library verification

From this directory:

    python code/research.py verify
    python code/research.py data --maximum 1000
    python code/research.py sample 20 --seed 381190

The first command performs a Python-only exhaustive check for n=3..7 and
checks the exact formulas through n=1000. It requires no third-party package.

To repeat the larger, independent C++ exhaustion:

    g++ -O3 -std=c++17 -Wall -Wextra -pedantic code/exhaustive.cpp -o exhaustive
    ./exhaustive 11 > data/exhaustive.csv
    python code/research.py verify --exhaustive-csv data/exhaustive.csv --report verification/exact_checks.json

On Windows with PowerShell 7 and g++, use `./exhaustive.exe` for the executable.
The C++ source also avoids compiler-specific bit-counting intrinsics, but only
the recorded GCC build was tested here. Each accepted row records n, set size,
induced edge count, and the complete integer vertex mask.

The vertex numbering is N=0, S=1, a_i=2+2*i, b_i=3+2*i. A sample is printed as
a set of these integer vertex indices. The independent acceptance predicate
uses only the graph, closed neighborhoods, private neighbors, and a connectivity
traversal; it does not use the classification to prune subsets.

## Optional symbolic audit

    python -m pip install -r requirements-optional.txt
    python code/verify_symbolic.py

The exact algebraic checks include the claimed generating functions, the
Perrin weighting identity, the Binet weights via a cubic-field matrix trace,
and rational inequalities proving the rounding bound. Floating-point checks
use 180 decimal digits through n=1000 and are supplementary, not substitutes
for the proofs.

## Build the PDF

Use a TeX Live or MiKTeX installation with newpx, amsmath, amsthm, mathtools,
TikZ, tcolorbox, listings, microtype, hyperref, cleveref, and the other packages
listed in the preamble. No external images, bibliography database, shell escape,
or font files supplied by this archive are needed.

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Three passes reliably settle the contents and cross-references. `make pdf`,
`make test`, and `make test-symbolic` are optional conveniences.

## Recorded checks

The independent C++ program examined all 22,369,536 subsets for n=3..11 and
accepted 926 sets in total. The full sets of vertex masks matched structural
generation exactly, as did their size/topology counts. All 40 published terms
matched. Exact identities, endpoint counts, divisibility, and strict
log-concavity were tested through n=1000; 900 sampled sets passed the independent
membership test. See the JSON reports for the actual saved results.

The PDF was compiled without reported overfull boxes or unresolved references,
rendered, and visually inspected. No automated submission to OEIS, publication,
or external account action was performed.
