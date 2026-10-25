# Signed Pell caps and free scale carriers

Round 16 research packet for ProveIt, 25 October 2026.

Start with `report/report.pdf`; the editable master is `report/report.tex`.

## Results

| Construction | Domain | Variables | Exact degree | Evaluation or expansion |
|---|---|---:|---:|---|
| Signed cap with odd quotient | unrestricted integers | 352 | 4 | 219 residuals; 9,355 monomials; height 15,020,718 |
| Signed cap with guarded quotient | unrestricted integers | 355 | 4 | 220 residuals; 9,370 monomials; same height |
| Free-scale first-root carrier | unrestricted integers | 15 | 44 | 111 live binary gates |
| Free-scale main saturation, sharp | unrestricted integers | 11 | 352 | 132 live binary gates |
| Main-and-guard product, native | unrestricted integers | 11 | 924 | 109 live binary gates |
| Main-and-guard product, short | unrestricted integers | 11 | 840 | 110 live binary gates |
| First polynomial radical correction | strictly positive integers | 10 | 253 | 102 live binary gates |
| Second polynomial radical correction | strictly positive integers | 10 | 252 | 104 live binary gates |

Six saturation siblings and two low-operation eleven-integer products are retained, not just the sharp free-scale endpoint. Most compact results are degree/cost tradeoffs; the two product endpoints strictly improve both degree and cost relative to 966/111 and 882/112. The 352-coordinate direct result belongs to the inspected small-coefficient direct-calculus class; native huge-coefficient quartics already use fewer variables. It is not a fewest-variable quartic overall.

Each zero-existence equivalence inherits the explicitly retained ordinary compiler/refutation calibration. Absence of a zero expresses Con(ZFC) at that calibration. These are not proofs of consistency, new global minimality results, or new end-to-end proof-assistant kernel certificates.

## Files

- `alternative/`: two direct quartics, every quadratic residual, fully expanded coefficients, projection/restoration and cap certificates, full proof and source closure.
- `lowdegree/`: complete 15-integer equation, literal DAG, exact degree proof and independent cut-register audit.
- `integer/`: six 11-integer saturation DAGs, complete formulas, proofs and exact leading-form certificates.
- `integer_lowops/`: two additional 11-integer single-product DAGs improving the low-operation frontier.
- `positive/`: two 10-positive-integer DAGs, complete coefficients, full proof and retained original compact44 parent.
- `review/`: independent mathematical and literal-data reviews with deterministic receipts.
- `baseline/`: pinned comparison frontier and explicitly selected source evidence.
- `prior/wave15/`: exact preceding release, retaining coherent transitive proof, coefficient-recipe and licensing dependencies.
- `report/`: TeX source, PDF and page-by-page QA receipt.

## Reproduction

The byte-identical receipt replay is pinned to Python 3.12.14 and SymPy 1.14.0. Standard-library-only branches do not need SymPy, but the complete independent review does. No network, machine simulation or consistency search is needed.

    python -B reproduce.py --receipt ../round16-replay/REPRODUCE_CHECK.json

This first validates the release inventory and reviewed code hashes, then regenerates outputs in isolated temporary copies in normal and optimized Python. It compares every listed output byte-for-byte and runs mutation and archive-integrity negative controls. Equations and DAGs are identical in both modes; receipts that record optimization state are compared to their corresponding normal or optimized reference, not to one another. Other Python/SymPy versions may preserve the mathematical outputs but change environment fields in audit receipts. It does not modify the original release.

To check the final ZIP too:

    python -B reproduce.py --archive ../ConZFC_Signed_Caps_Free_Scales_2026-10-25.zip --verify-only

TeX compilation is separate:

    sh report/build_report.sh

The script writes its PDF and temporary TeX products in the sibling `ConZFC_Signed_Caps_Free_Scales_tex_rebuild/` directory, preserving the sealed release. The included PDF was compiled and visually inspected. Rebuilding a PDF may change bytes with another TeX installation; the deterministic Python and ZIP claims do not assert toolchain-independent PDF bytes. `MANIFEST.json` excludes only itself and never-distributed Python cache files. Review provenance and code before running a release: its manifest is not a signature or mathematical proof.

No repository write, commit, issue, or third-party publication was performed.
