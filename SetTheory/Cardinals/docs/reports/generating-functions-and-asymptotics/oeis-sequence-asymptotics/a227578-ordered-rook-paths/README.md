# Ordered long jump rook paths

This package accompanies **Ordered Long Jump Rook Paths: Exact coefficient identities and fixed dimension asymptotics**, dated 2 October 2026.

## Results

For OEIS A227578 and each fixed integer dimension k >= 2, the article proves an exact rational coefficient identity and a full asymptotic expansion to every fixed algebraic order. It gives the general leading constant, the first two corrections, a finite all-order generator, rational dependence of each correction on dimension, a D-finite generating-function consequence, and a specified-model Lambert W inverse with recursive corrections.

The small-dimensional leading constants are prior OEIS statements. Classical orbit, smooth-point, Gaussian and Lambert W methods are credited in the article. No exhaustive novelty certification, growing-dimension uniformity, certified posted recurrence, or effective finite-n error bound is claimed. Counts are nondecreasing; A(0,k)=A(1,k)=1. The continuous inverse approximation is not a certified integer threshold.

## Files

- `ordered_rook_paths.pdf`: the research article
- `ordered_rook_paths.tex`: editable self-contained TeX source, with bibliography
- `code/generate_coefficients.py`: arbitrary fixed-order, exact coefficient generator; integer or symbolic dimension
- `code/evaluate_model.py`: numerical forward and specified inverse models through the two displayed corrections
- `code/check_models.py`, `check_unsymmetric.py`, `check_symmetric.py`: three direct combinatorial/coefficient comparisons
- `code/check_first_correction.py`, `check_wick.py`, `check_radial_and_wick.py`: first correction and independent Gaussian/algebraic checks
- `code/check_second_pairings.py`: general second correction from explicit Wick pairing enumeration
- `code/check_second_independent.py`: separate root substitution and Gaussian integration-by-parts verification
- `code/check_saddle_k3.py`, `check_saddle_k3_order2.py`: independent eliminated-coordinate saddle checks
- `code/check_inverse.py`: exact inverse-recursion cancellation through degree four
- `code/check_numerics.py`: recurrence-free larger direct counts and approximation errors
- `data/`: deterministic reference results, intermediate symbolic polynomials and the article table
- `SOURCES.md`: public source and version notes
- `VALIDATION.md`: verification scope and limitations
- `requirements.txt`: pinned Python requirements
- `MANIFEST.sha256`: hashes of every release file except the manifest itself
- `safe_extract.py`: conservative ZIP extraction helper
- `replay.sh`, `build.sh`: complete replay and PDF rebuild

## Reproduce

Requirements: Python 3.10 or later, SymPy 1.14.0, mpmath 1.3.0, Bash, and a TeX installation providing pdfLaTeX, Latin Modern, AMS packages, geometry, booktabs, microtype, hyperref and enumitem. Poppler is needed only to render page images for visual inspection.

From the extracted package directory:

    python3 -m pip install -r requirements.txt
    bash replay.sh

The replay verifies the manifest before running, regenerates every packaged result file, compares the parsed JSON values or exact text, rebuilds the PDF, requires byte-identical output, and rechecks all pinned hashes. It writes temporary results under `.replay/` and TeX intermediates under `.build/`. No network access is needed after dependencies have been installed.

On the verification machine the full replay is a short computation; substantially higher symbolic orders can become expensive. The reference generator favors clarity and exactness over high-order optimization.

To rebuild only the PDF:

    bash build.sh

To use the finite generator:

    python3 code/generate_coefficients.py --k 3 --order 2
    python3 code/generate_coefficients.py --k symbolic --order 2

`--order J` returns d_0 through d_J. The symbolic-dimension option performs a universal power-sum calculation and then degree-lowering Gaussian integration by parts. It does not infer a formula by fitting several dimensions. No counting recurrence is used.

To evaluate a model:

    python3 code/evaluate_model.py forward --k 3 --n 80 --order 2
    python3 code/evaluate_model.py inverse --k 3 --target 1e100 --order 2

The `order` argument here is the number of retained correction terms, 0, 1 or 2. The inverse command returns the carrier inverse and the recursive approximation to the explicitly named logarithmic model. It deliberately does not round to a purported certified threshold.

## Safe extraction

If this helper is available outside the archive, use:

    python3 safe_extract.py ordered-rook-reproducibility.zip new-directory

It requires a new destination and rejects absolute paths, traversal, duplicate members, symbolic links, special files and oversized archives. The ZIP contains one `ordered-rook-report/` top-level directory. Before running downloaded code, inspect its contents and provenance. The manifest detects accidental changes; it is not a cryptographic identity signature.

All included computations and data are for this article. Full third-party papers and unproved recurrence-derived higher coefficients are not distributed.
