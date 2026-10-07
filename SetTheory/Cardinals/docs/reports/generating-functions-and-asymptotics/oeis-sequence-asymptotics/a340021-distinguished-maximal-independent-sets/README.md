Report206
Graphs with a distinguished maximal independent set
All fixed order expansions and inverse thresholds for OEIS A340021
4 October 2026

CONTENTS
Report206.tex and Report206.pdf: standalone article, complete proofs and sources
verify_exact.py: standard-library rational and integer verification
independent_checks.py: independent permutation/inclusion-exclusion and symbolic checks
diagnostics.py: 220-decimal-digit numerical illustrations, not interval certificates
build.py: complete deterministic regeneration and packaging
exact_results.json, independent_results.json, diagnostics.json, checks.json: generated data
tables.tex: every printed table cell, generated from the programs' output
requirements.txt: Python dependency versions
MANIFEST.json: SHA-256 digests of all other archive files

REBUILD
Use Python 3.10 or later, the pinned dependencies in requirements.txt, and
pdfLaTeX with standard amsmath, amsthm, mathtools, lmodern, microtype,
geometry, booktabs, longtable and hyperref packages.
Run:
    python build.py
In a separate archive extraction, run:
    python -O build.py
Both regenerate all data, table source, PDF, manifest and Report206.zip.
The archive uses sorted, uncompressed entries and fixed timestamps; PDF
metadata dates and random identifiers are disabled. Complete ZIP bytes are
expected to match with the same Python, SymPy, mpmath and TeX environment.
Recorded environment: Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0,
pdfTeX 1.40.26 (TeX Live 2025/dev/Debian). If the installed TeX format is
missing, the build initializes a private format from installed TeX sources
in a temporary directory. Shell escape is disabled. No TeX binary is downloaded.
The build invokes six deliberately false checks in normal and optimized
Python and requires all six to fail. No correctness guard uses assert.

The first exact verifier uses only the standard library and can be run alone:
    python verify_exact.py
    python -O verify_exact.py

INTERPRETATION
The exact/formal checks certify the finite identities they test. They do not
establish asymptotic remainder constants or effective onsets. Floating data
use a documented finite series cutoff and are illustrative, not rigorous
interval computations. Inverse constants and onsets in the article are
existential. The integer-safe conclusion is a two-ceiling envelope, not an
unconditional single-ceiling rounding formula.

Source scope: 20 displayed OEIS terms checked from an inspected cached
snapshot. Direct raw entry/b-file access failed. No claim covers the full
b-file or every later OEIS revision. The article credits classical
maximal-clique expectation, logarithmic growth, shrinking-width, rigidity,
colored-graph, and depoissonization prior. No global priority claim is made.

PUBLIC MATERIALS ONLY
This archive includes newly written report and code materials. It does not
redistribute any third-party PDF, internal note, private report or credential.
All literature is referenced by public links in Report206.pdf/tex.
