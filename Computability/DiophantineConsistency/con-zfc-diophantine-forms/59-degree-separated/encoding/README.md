# Degree-separated quadratic source encoding

The new source architecture uses three homogeneous kernels,
G = D2 U^2 + D1 U + D0, rather than the square of a word with a dummy 1.
Only same-degree monomials can contaminate one another. The linear source
monomial N and quadratic source monomial J^2 deliberately share label 2.

The frozen code has maximum variable label 116, maximum target 2129, and
exact convolution height 2161. Its 89 weighted records extract precisely
twice 22 residuals equivalent to the complete original 31-variable parent.
The height is 61.10% smaller than the wave7 value 5556. These source metrics
are not final polynomial degrees; compose and audit the chosen finalizer.

Canonical proof/replay files:

- parent_source.json: the unchanged original package31 source, pinned by SHA256.
- split_code.json: the frozen label and target certificate.
- split_kernels.json: all three kernels with exact four-port coefficient recipes.
- verify_split.py: independent standard-library formal polynomial checker.
- VERIFICATION.json: its exact receipt.
- test_split.py and TEST_RESULTS.json: isolated normal/-O replay and ten rejected corruptions.
- SPLIT_SOURCE_PROOF.md and section.tex: full source theorem and bounds.
- report.tex and report.pdf: standalone mathematical appendix.
- SOURCE_PINS.json: lineage and exact source hashes.

The proof establishes positivity of G for every g>=0 before digit recovery.
For adapters requiring positivity for every integer packed input, the optional
G+B^2162 variant is positive for every real input and increases height by only 1.
Use the complete old 31 native coefficient tuple; MF is already shifted. The
source 52 transport convention is not interchangeable without adapting row 15.

From this directory:

    python3 verify_split.py
    python3 test_split.py
    python3 -O verify_split.py

All replay steps are read-only. Regenerating the derived kernels is optional:

    python3 verify_split.py --write

Ordinary and optimized Python receipts are byte-identical. No external
symbolic package, network, search binary, or sibling archive is required.

The remaining search files and their logs are optional discovery provenance,
not proof dependencies. No global optimum or end-to-end kernel certificate
is claimed. The unbounded compiler/refutation and finalizer theorems remain
explicit inherited dependencies of the enclosing construction.
