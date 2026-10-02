# Asymptotic enumeration of tied football seasons

This package gives a proof and reproducible finite calculations for OEIS A380592: the number of seasons in a double round-robin football league in which all labeled teams finish with the same score. The two matches per pair are distinguished; each match uses the usual 3/1/0 scoring rule.

Read `tied-football-asymptotics.pdf`. The editable source is `report/tied-football-asymptotics.tex`.

## Mathematical coverage

The report proves:

- The leading equivalent, with its essential three-residue theta factor and the common-score center shift of −13/84
- Sharp global Fourier localization, including the negative-quartic Gaussian majorant and the outlier integral bound
- Mean-matching exponential tilts, dominated summation over all common integer scores, and the limiting discrete-Gaussian conditional score law
- An expansion to every fixed inverse-power order, by checking the independent-coordinate mixed-difference hypotheses of Isaev's complex cumulant theorem
- A finite exact Gaussian-moment algorithm for every coefficient, and the explicit first correction polynomial Q
- Residue-aware ceiling enclosures for the inverse counting threshold, including the boundary uncertainty

Primary sources and the scope of a bounded literature search are given in the report. No exhaustive novelty claim is made.

## One-command replay

Requirements: Python 3.10 or newer and SymPy 1.14.0. The Python scripts use no network access and do not need LaTeX. Tested with Python 3.12.14 and SymPy 1.14.0.

From the extracted package root:

```sh
python -m pip install -r requirements.txt
python replay.py
```

Dependency installation is a one-time setup. `python replay.py` is the single replay command. It recomputes every check and exits nonzero if a calculation fails or differs from its frozen expected result. Allow several minutes, depending on the computer.

By default, generated results are written to `replay_outputs/`. To keep them elsewhere, use a fresh directory:

```sh
python replay.py --output-dir /path/to/fresh/results
```

The `expected/` directory contains frozen reference JSON; the replay never updates it. Exact rational expressions, symbolic polynomials, integers, decimal strings, and JSON structure are compared exactly. Ordinary floating-point diagnostics use relative tolerance 5e-13 and zero absolute tolerance. Those diagnostics are not interval certificates.

## Verification scripts

- `code/leading_term_checks.py`: one-match cumulants, 135 symmetric-polynomial identities, leading constants, independent exact enumeration for n = 1, 2, 3, 4, and clearly labeled small-n comparisons
- `code/symbolic_identity_checks.py`: the general-q quartic, aggregated cubic and quartic, and the completed-square constants
- `code/first_correction_checks.py`: exact power-sum Gaussian pairing calculations for the moments entering the first correction
- `code/cumulant_filtration_checks.py`: an alternative dynamic set-partition aggregation of raw moments and cumulants through order six, including vanishing fifth and sixth cumulants through grade 1/n
- `code/finite_n_gaussian_checks.py`: exact rational Gaussian-cumulant evaluations at n = 20, 50, 100, 1000, together with decimal diagnostics
- `code/independent_ibp_checks.py`: direct single-match logarithmic Taylor expansion and a Gaussian integration-by-parts recurrence, checking the first-correction moments, omitted fourth-cumulant mixtures, general-q local correction, tilt, determinant, carrier, and Q
- `code/residue_constants_checks.py`: numerical theta factors, first corrections, and conditional score means and variances on the three residue classes
- `code/gaussian_moments.py` and `code/output_support.py`: shared finite-moment and output helpers

Each check has a corresponding frozen JSON file in `expected/`. The independently derived algebraic results are retained in those readable files, rather than only a pass/fail statement.

## Rebuild the PDF

Requirements: Bash and a working pdfLaTeX installation with the standard packages `fontenc`, `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `booktabs`, `microtype`, `hyperref`, and `enumitem`. TeX Live 2025 was used for the supplied PDF. No BibTeX run is needed.

From the package root:

```sh
bash build-report.sh
```

The script runs three TeX passes and replaces the package's PDF with the rebuilt copy. Build intermediates go to `replay_outputs/latex/`. It uses package-relative locations and includes a fallback for read-only Debian TeX trees missing generated format or filename-database files. A fixed source date is set; byte-identical PDF output across different TeX/font versions is not promised.

The SHA256 manifest describes the supplied release, so a rebuilt PDF may have a different checksum. Preserve the original extracted copy if you want to verify the original manifest afterward.

## Integrity

Before replay or rebuilding, from the package root:

```sh
sha256sum -c MANIFEST.sha256
```

The manifest lists every distributed regular file except the manifest itself. Generated outputs, bytecode, TeX build products other than the final PDF, and inspection images are not included in the archive.

## Limits

The analytic proofs establish every **fixed** order. They do not assert convergence of the infinite expansion, uniformity for an order growing with n, effective numerical remainder constants, or a certified small-n approximation range. The inverse ceiling bounds are eventual theoretical bounds; their constants and onset have not been made effective.

The programs implement the stated finite coefficient checks. The report specifies a finite arbitrary-order algorithm mathematically, but this package is not an optimized general-purpose arbitrary-order engine. The integration-by-parts program computes selected moments to an extra grade as an algebraic check; it does not claim to supply the complete second asymptotic correction.

Known exact counts for n = 5 through 8 are taken from the primary enumeration paper and OEIS, not recomputed here. Small-n ratios neither certify a remainder nor validate the 1/n coefficient by a numerical fit. The first correction is established by exact algebra and the analytic omission bounds.

The archive contains the report and its verification material. It does not redistribute any cited paper. Follow the primary-source links in the bibliography to read those papers.
