# Precise asymptotics of the powered Catalan numbers

This package accompanies the 14-page report for OEIS A113227, dated 1 October 2026.

## Main result

With w = W(n/e) and r = n/w,

    a_n ~ e^(-2) r^(n-3/2) exp(r-n) / sqrt(2*pi*(w+1))
        ~ e^(e-2)/sqrt(2*pi) * r^(-3/2) * B_n(e).

The report proves a positive discrete Bessel moment representation, the complete large-node asymptotics, an expansion to every fixed algebraic order, a canonical continuous inverse, and an entire exponential-generating-function corollary. It displays the first two correction functions and specifies an exact algorithm for every correction.

The known recurrence, path models, and formal continued fraction are explicitly attributed. The literature review is scoped and is not a certification of global novelty. Conventional expert peer review remains appropriate before publication.

## Read first

- powered-catalan-asymptotics.pdf: complete mathematical report
- powered-catalan-asymptotics.tex: editable source
- mathematical-verification.md: independent review of the exact final source
- SOURCE_NOTES.md: known starting points and the scope of the literature check
- VALIDATION.md: numerical, rendering, and replay checks

## Reproduce

Required: Python 3.10 or later, mpmath, SymPy, and a standard pdfLaTeX installation with amsmath, amssymb, amsthm, geometry, lmodern, microtype, hyperref, booktabs, and enumitem. Tested versions are in requirements.txt and environment.txt.

From this directory:

    python -m pip install -r requirements.txt
    bash run_checks.sh

The replay runs all symbolic and numerical computations and then rebuilds the PDF. It writes the same named output files in this directory. The TeX build uses a fixed source date for reproducibility; on the tested toolchain the PDF is byte-identical after clean replay. Other TeX versions can produce different PDF bytes without changing the mathematics.

To build only the PDF:

    bash build.sh

To check the release files before and after replay:

    sha256sum -c SHA256SUMS

## Programs and outputs

- residue_expansion.py: exact formal reciprocal-product and Stirling coefficients through order seven; residue-output.txt
- saddle_expansion.py: exact Gaussian-moment coefficient extraction through c_4; saddle-output.txt and saddle_coefficients.txt
- verify_coefficients.py: exact integer recurrence through n=2500 and comparison with c_1 and c_2; coefficient-output.txt and coefficient_checks.json
- verify_spectral_moments.py: 110-digit Bessel node/weight diagnostics with 65 nodes, total mass and exact-moment comparisons through n=30; spectral-output.txt
- verify_inverse.py: H_J inverse diagnostics against exact recurrence targets through n=500 for J=0,1,2; inverse-output.txt and inverse_checks.json

## What is and is not certified

The proof establishes fixed-order asymptotic remainder scales. Numerical tests are high-precision diagnostics, not interval computations or proof-assistant certificates. A numerical Newton residual controls the root of the truncated H_J equation; a certified finite-target enclosure of the true inverse additionally requires an explicit bound for the asymptotic remainder. The report makes this distinction explicit.

The algebraic expansion is a Poincare expansion, not an exponentially complete transseries. No claim of convergence of the infinite correction series is made. No external upload or submission is part of this package.

For higher symbolic orders, increase M in residue_expansion.py and J in saddle_expansion.py, keeping M at least J. The finite exact formulas in the report justify every such fixed order; computation time and expression size grow with the order.
