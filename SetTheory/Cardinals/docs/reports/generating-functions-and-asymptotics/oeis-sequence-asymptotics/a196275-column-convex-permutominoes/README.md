# Exact asymptotics and inversion for column-convex permutominoes

Research report for OEIS A196275, 2 October 2026.

## Read first

- `pdf/permutomino_asymptotics.pdf`: the complete 14-page mathematical report
- `source/permutomino_asymptotics_standalone.tex`: editable standalone LaTeX source
- `source/permutomino_asymptotics.tex` and `source/validation_summary.tex`: equivalent modular sources
- `verification/README.md`: reproducible exact, symbolic, spectral, and inverse checks

The report proves the exact factorial-normalized generating function, exact Lambert-W growth constant and prefactor, positive spectral representation, complete mixed secondary asymptotics, specified interpolation's convergent inverse sectors, all-positive-index inverse rounding, and non-P-recursiveness. Numerical tests are supporting checks, not the proof. The literature search was bounded and does not establish exhaustive novelty.

## Compile

On an ordinary TeX installation, run twice from `source/`:

    pdflatex permutomino_asymptotics_standalone.tex
    pdflatex permutomino_asymptotics_standalone.tex

The included `source/build_local.sh` reproduces the modular PDF in the Debian/TeX Live environment used for this report, including its locally generated format. It writes a `build/` directory and `pdf/permutomino_asymptotics.pdf`. Packages used include amsmath, amssymb, amsthm, mathtools, lmodern, microtype, geometry, hyperref, xurl, booktabs, enumitem, graphicx, and fancyvrb.

## Reproduce the checks

Requirements: Python 3.12, mpmath 1.3.0 and SymPy 1.14.0. From `verification/`:

    python verify_a196275.py
    python -O verify_a196275.py --output verification_results_optimized.json
    python render_validation_tables.py

The frozen OEIS b-file is supplied; the verifier makes no network requests. Both normal and optimized-mode runs passed. See the verification README for precision, ranges, diagnostics, and limitations. The two exact-count JSON outputs are identical; both are retained to document the independent normal and optimized runs.

The verification table renderer uses the local symbol F for the Gamma envelope; the report's table fragment uses the symbol E to avoid collision with its log-envelope F. Numerical values are unchanged.

## Sources and reproducibility

Original published articles are cited and linked in the report. Third-party article PDFs, extracted text, and page images are not redistributed. The source manifest records the primary recurrence PDF and OEIS table hashes. `manifest.json` records all delivered file hashes. The report is an analytical derivation, not a claim of formal proof-assistant verification or certified interval quadrature.
