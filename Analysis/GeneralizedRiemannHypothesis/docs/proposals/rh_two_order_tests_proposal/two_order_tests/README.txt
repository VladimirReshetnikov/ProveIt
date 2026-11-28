TWO ORDER TESTS INSTEAD OF PRIMITIVE POLYNOMIAL LABELS
====================================================

This archive contains a technical proposal to simplify one local arithmetic
input to the supplied ProveIt theta-lift proof of RH and Dirichlet GRH.

Start with two_order_tests.pdf (16 pages) or its complete LaTeX source,
two_order_tests.tex. The mathematical statement and proofs are in Sections
5-7; the exact source integration map is in Section 9.

Main result
-----------
For q a prime power, r=3^a with a>=1, 6|M, and M^2|q-1, select nonzero
roots z in F_(q^r) by

    z^((q^r-1)/2) != 1,
    z^((q^r-1)/3) != 1,
    z^(3*(q^(r/3)-1)) != 1.

There are exactly (q^r-3*q^(r/3)+2)/(3*r) selected monic irreducible
degree-r polynomials. These roots retain degree r after every prime-power
operation and survive the original M-torsion scalar normalization.

The only source consumer of the full scalar-order divisibility can use
6^(s+6) instead of q2(s). With that explicit internal interface change,
one block's bad projector share becomes

    f*epsilon + exp(-f/(6*r)).

Both actual level primes are retained. Their exponential error terms add.
The original tame modulus M, allowed-polynomial condition, and square
congruence are retained.

Status
------
The local mathematics is proved in the report. Four standalone supporting
Lean theorems compile with the project's pinned Mathlib and no sorryAx.
The finite-field count and the changes across the GRH source files have
NOT been fully integrated or rebuilt. The original project's complete
RH/GRH build was NOT rerun as part of this review.

The non-overlap audit covers all five existing proposal directories,
including future-work sections, at the pinned source revision below.

Contents
--------
two_order_tests.tex            Complete report source.
two_order_tests.pdf            Compiled and visually reviewed report.
Lean/PowerOrbit.lean           Four checked supporting theorems.
Lean/lean_check.log            Compiler command, version pins, and axiom output.
Lean/README.txt                Exact formal scope and reproduction instructions.
checks/check_two_test_labels.py
                              Final fixed-2,3 integer checker.
checks/check_robust_labels.py  Shared helpers and earlier M-full checker.
checks/two_test_labels_results.json
                              Final deterministic results and examples.
checks/robust_labels_results.json
                              Conservative variant, clearly distinguished.
checks/checks_qa.txt           Independent rerun/determinism record.
checks/label_count_comparison.csv
                              Exact primitive-vs-selected polynomial counts.
provenance/source_anchors.tsv  28 source anchors with immutable URLs and hashes.
provenance/proposal_inventory.csv
                              20 textual proposal sources in five directories.
provenance/verify_provenance.py
                              Verify recorded source hashes against a checkout.
verification.txt              Final packaging and PDF verification record.
SHA256SUMS                    Checksums of the delivered files except itself.

Rebuild the PDF
---------------
Requires pdflatex and standard TeX Live packages (amsmath, amsthm, lmodern,
geometry, hyperref, bookmark, microtype, booktabs, tabularx, longtable, xurl).
From the extracted archive directory:

    pdflatex -interaction=nonstopmode -halt-on-error two_order_tests.tex
    pdflatex -interaction=nonstopmode -halt-on-error two_order_tests.tex

Rerun the exact finite checks
----------------------------
Requires Python 3.10 or newer; only standard-library modules are imported.
Do not run Python with -O, because the checks deliberately use assertions.
Run from the extracted archive directory:

    python3 checks/check_two_test_labels.py --output two_test_rerun.json
    python3 checks/check_robust_labels.py --output robust_rerun.json

The final fixed-two-test script imports the shared checker, so keep both
Python files together. Results are deterministic. The checked JSON files
can be compared byte-for-byte with the regenerated files:

    cmp checks/two_test_labels_results.json two_test_rerun.json
    cmp checks/robust_labels_results.json robust_rerun.json

The fixed-two-test run inspects 1,754,908 exponents, makes 2,799,874 full
primary-removal checks, and makes 3,610,932 scalar-scaling checks. Three
small fields are exhaustive; larger cases are deterministic samples.
The JSON explicitly distinguishes the two modes.

Recheck Lean
------------
Use Lean 4.35.0 and a Mathlib checkout at

    56a005855ea17e0b0958f73ec801ae140b0a1679

After obtaining that checkout's dependencies and compiled cache, run
from the Mathlib directory:

    LAKE_JOBS=1 lake env lean /absolute/path/to/Lean/PowerOrbit.lean

See Lean/README.txt for all theorem hypotheses and the finite-field bridge
that remains to be implemented. A successful run checks this supplement,
not the modified GRH development.

Verify source provenance
------------------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Audited commit: 89d12dd40424f1217fd818d84877b3da52396a3b

With a local checkout of the relevant source and proposal files:

    python3 provenance/verify_provenance.py /absolute/path/to/ProveIt

The verifier checks SHA-256 and Git blob hashes for 48 records covering
35 distinct files and all five proposal directories. The archive contains
source references and new analysis, not a copy of the original repository.

Integrity
---------
On systems with sha256sum, from this archive directory:

    sha256sum -c SHA256SUMS

The PDF bytes, TeX source, checked Lean source, and generated JSON outputs
are covered by the manifest. Recompiling the PDF can change its metadata
and checksum without changing the mathematical content.
