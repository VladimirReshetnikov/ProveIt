THREE ADVANCES ON OEIS CONJECTURES AND ASYMPTOTICS
Bridgeless toroidal maps, golden-ratio moment laws,
and unitary-divisor partitions

Prepared with ChatGPT, 4 October 2026 UTC.
Based on the ProveIt repository maintained by Vladimir Reshetnikov.

CONTENTS

oeis_advances.pdf       Complete research article.
oeis_advances.tex       Standalone LaTeX source, including bibliography.
code/                  Four reproducible verification programs.
data/                  Dynamics, renewal, and partition verification output.
verification/          Exact map-verification output.
README.txt             This guide.

The TeX source has no external section inputs, figures, bibliography database,
or downloaded assets. It can be compiled on its own. The supplied PDF is the
result of compiling this source, with cross-references resolved.

RESULTS

1. A343093: proof of the square-convolution generating function posted as a
   conjecture; positive finite formulas; three explicit asymptotic terms.

2. A088714/A088713: strictly positive real-analytic moment densities on the
   entire positive half-line, with sharp origin and derivative equivalents;
   a nonzero real-analytic antiperiodic transform-correction profile;
   a convergent inverse-logarithmic expansion with separately controlled
   exponentially small discrepancies; a general full fixed-shift renewal
   expansion and the sharper comparison of the companion coefficients.

3. A301981/A301982: each ratio to its pure OEIS asymptotic model has liminf 0
   and limsup infinity; two-sided logarithmic oscillations of at least
   order n^(1/4), explicit symbolic lower constants, and corresponding
   inverse-model oscillations.

The article states exactly which results are new in this work and which
are imported from the repository or primary literature. The fine Bell-number
normalization for A088714 remains open. A bounded literature search is not
an exhaustive priority search. This manuscript has received internal
mathematical review but has not been externally refereed or formalized in
a proof assistant. No OEIS update, repository change, or external submission
was made as part of this work.

BUILD THE PDF

From the directory containing oeis_advances.tex:

    latexmk -pdf -interaction=nonstopmode -halt-on-error oeis_advances.tex

Alternatively run pdflatex three times. A normal TeX Live or MiKTeX
installation with the following standard packages suffices:

    fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
    booktabs, longtable, array, tabularx, graphicx, xcolor, microtype,
    enumitem, xurl, hyperref, fancyhdr.

REPRODUCE THE COMPUTATIONAL CHECKS

Run these commands from this directory, without Python's optimization
flag (-O), because several checks use assertions:

    python3 code/verify_maps.py
    python3 code/verify_dynamics.py
    python3 code/verify_renewal.py
    python3 code/verify_partitions.py --output data/partition_verification.json

The programs require no network access. Python 3.12.14 was used for the
supplied outputs. The dynamics, renewal, and partition programs use only
the standard library. The map program additionally uses SymPy 1.14.0 and
mpmath 1.3.0 in the recorded run. They can be installed with:

    python3 -m pip install sympy mpmath

All four final runs passed. The map program compares two exact formulas
through n=100, verifies all 20 stored OEIS terms, enumerates rotation systems
through four edges, and checks symbolic algebra. The dynamics program
computes exact rational Stieltjes bounds and propagates outward-rounded
100-digit Decimal intervals through 115 inverse steps. Its nonzero
profile certificate is part of the proof. The renewal program verifies
independent formal coefficients and 16,383 exact compositions; the partition
program verifies two independent coefficient constructions through n=160.

Finite prefix agreement and numerical asymptotic diagnostics are checks
of implementations and constants, not proofs of infinite asymptotic claims.
The latter are established by the written arguments in the article.

PINNED SOURCES

Repository:
https://github.com/VladimirReshetnikov/ProveIt

Snapshot:
eaf08931cbfd0132dd36ab82a7743ccb02506dc7
Commit timestamp: 2026-10-04T00:59:12Z.

Inherited A088714/A088713 research article:
https://github.com/VladimirReshetnikov/ProveIt/blob/eaf08931cbfd0132dd36ab82a7743ccb02506dc7/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth/article.tex

Inherited partition research article:
https://github.com/VladimirReshetnikov/ProveIt/blob/eaf08931cbfd0132dd36ab82a7743ccb02506dc7/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a301981-unitary-divisor-partitions/article.tex

OEIS entries inspected on 4 October 2026 UTC:
https://oeis.org/A343093
https://oeis.org/A088714
https://oeis.org/A088713
https://oeis.org/A301981
https://oeis.org/A301982

Full literature references and precise theorem dependencies are included in
the article. The prior repository manuscripts are not repackaged as new work.
