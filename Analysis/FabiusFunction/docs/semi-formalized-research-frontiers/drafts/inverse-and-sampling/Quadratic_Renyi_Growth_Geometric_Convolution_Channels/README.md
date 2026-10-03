# Quadratic Rényi Growth
## A Universal Linear Correction and Endpoint Selection in Geometric Convolution Channels

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

The article answers the question **“Growth above the critical Rényi order”** in the
ProveIt draft *Beyond Polynomial Diagonals: Nuclear Bayesian Operators, Exact Null
Modes, and a Rényi Phase Transition for Fabius–Rvachev Laws* (29 September 2026).
The inspected source is pinned in `PROOF_AUDIT.md` and in Section 11 of the article.
No files in the GitHub repository were modified.

## Result

Let `0 < q < 1`, `L = log(1/q)`, and let `U_j` be independent uniform variables on
`[0,1]`. Set `X=(1-q) sum_{j>=0} q^j U_j` and let `S_m` be its first `m` terms.
For every fixed `alpha > 2`, the article proves

    I_alpha(S_m;X) = (alpha-2) L m^2 / 2 + B(alpha) m + O(log(m+1)^2),

    B(alpha) = alpha(alpha-2)/(alpha-1) log(alpha)
               - (alpha-1) log(alpha-1).

Here `I_alpha = D_alpha(P_{S_m,X} || P_{S_m} x P_X)`; it is not Sibson or Arimoto
information. Both coefficients are multiplied by `max(theta_0,theta_1)` for
Beta(theta_0,theta_1) innovations with both parameters at least one. The article
also proves endpoint selection and radial/allocation large-deviation principles
under the probability measure tilted by the Rényi integrand.

The theorem is for fixed parameters. It does not establish the joint crossover
`alpha=2+u/m`, nor does it assert a uniform error as `q` approaches one.

## Contents

- `article.pdf`: the 20-page article (19 as delivered; the editorial notes
  of 2026-09-30 add one), including detailed proofs, provenance,
  validation boundaries, and nine further research questions.
- `article.tex`: complete LaTeX source, with embedded bibliography.
- `checks/verify.py`: exact algebra and dyadic-density checks plus optional
  floating-point endpoint quadrature.
- `checks/verification.json`: recorded exact checks and point diagnostics.
- `checks/saddle_rows.tex`: recorded generated table used by the LaTeX source.
- `checks/quadrature_24.json`, `checks/quadrature_32.json`: optional windowed
  quadrature runs, with their limits explicitly recorded.
- `requirements.txt`, `Makefile`: dependencies and rebuild commands.
- `PROOF_AUDIT.md`: proof dependencies, computational checks, and limitations.
- `SHA256SUMS` (not kept): the delivered checksum ledger (11 entries) was
  verified in full on filing (batch 65) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`, batch 65
  row).

## Rebuild the PDF

A TeX installation providing AMS packages, New PX fonts, geometry, microtype,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr, xurl, hyperref,
cleveref, and aliascnt is sufficient. No external image or bibliography files
are needed; the generated table is retained in the package.

    make pdf

Without `make`, run the following command three times in this directory:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex

## Reproduce the checks

Python 3.10 or later is recommended.

    python -m pip install -r requirements.txt
    python checks/verify.py --dps 100

This regenerates `verification.json` and `saddle_rows.tex` in `checks/rerun/`;
only `--output checks` overwrites the recorded files, including the table the
article inputs (as delivered, the default was `checks/` itself).
Optional runs used for the supplied diagnostics are:

    python checks/verify.py --quadrature 8 12 --nodes 24 --dps 80
    python checks/verify.py --quadrature 8 12 --nodes 32 --dps 100

They write `quadrature_24.json` and `quadrature_32.json`, also to
`checks/rerun/` by default. In this repository, on Windows, `uv run
--no-project --with sympy==1.14.0 --with mpmath==1.3.0 python
checks/verify.py --dps 100` runs the check without a virtual environment
(add `--with numpy==2.3.5` for the quadrature runs); bare `python` may not
resolve, so use `py` or `uv`.

The script uses exact Fraction/SymPy arithmetic for its algebraic identities and
dyadic values. Logarithms and numerical quadrature are floating-point. The
quadrature omits the middle region and truncates the radial domain; the analytic
omitted-density-term bound does not include floating-point rounding. Consequently
these estimates are **not certified values of the complete Rényi information**.

## Research and verification status

The analytic results are proved in the text. No Lean/Rocq proof, independent
peer review, or exhaustive literature-wide priority verification is claimed.
The source and PDF are the deliverable, not an automatic modification of ProveIt.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`.
The addressee line ("prepared for Vladimir Reshetnikov") is kept as
delivered, as for the earlier arrivals of this directory.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). Three notes:
  - after the paragraph following Proposition `prop:subcritical`: the
    predecessor results reproved in `prop:subcritical` and
    `prop:finiteness` are Theorems `thm:renyi-phase` and `thm:all-renyi` of
    `../Nuclear_Bayesian_Operators_Fabius_Rvachev_Laws/` (second proofs for
    uniform innovations, the beta extension new); the limits agree under
    `X_old = 2X - 1`, the predecessor's "second integral" at `alpha = 2`
    being 2 there and 1 here;
  - after Proposition `prop:dyadic`: the uncited Lean counterparts of the
    dyadic density values at `q = 1/2`
    (`Fabius.ProbabilityRepresentation.geometricUniformDensity_one_half_eq_rvachevUp`,
    `Fabius.fabiusDyadicValue_cast`, `Fabius.fabiusReal_quarter`,
    `Fabius.fabiusReal_three_quarters`, `Fabius.deriv_fabiusReal_half`,
    all under `Analysis/FabiusFunction/Lean/FabiusFunction/`); no Rényi
    statement has a Lean counterpart;
  - after the research question "A uniform critical crossover": it is the
    predecessor's question "Critical crossover", open in both.

  Two marked corrections: the `cleveref` plural names "corollarys" and
  "Corollarys" now read "corollaries" and "Corollaries" (no plural
  corollary reference is printed), and in the proof of Theorem
  `thm:beta-main` "the larger `theta_e`", used before `theta_e` is
  defined in Section 6, now reads "the endpoint with the larger exponent
  `theta_0` or `theta_1`". No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source by the three `pdflatex`
  passes of the `Makefile` (MiKTeX pdfTeX 1.40.29): 20 pages (19 as
  delivered), no error, undefined reference or citation, multiply defined
  label, duplicate destination, or overfull box; every font is embedded and
  none is Type 3. The pages carrying the notes were rendered and inspected.
- `checks/verify.py`: the default `--output` is `checks/rerun/` instead of
  `checks/`, so a plain run no longer overwrites the recorded
  `verification.json`, the quadrature records, or `saddle_rows.tex` (which
  the article inputs); every file is written with LF line endings on every
  platform (as delivered, the platform's, so CRLF on Windows). A rerun of
  the amended program on a copy (2026-09-30, Python 3.14.4, SymPy 1.14.0,
  mpmath 1.3.0; NumPy 2.3.5 for the quadrature) reproduced
  `checks/verification.json`, `checks/saddle_rows.tex`,
  `checks/quadrature_24.json` and `checks/quadrature_32.json` byte for byte.
- `PROOF_AUDIT.md`: a dated amendment under "PDF and package checks" records
  the retired ledger and the rebuilt PDF.
- `README.md`: the PDF page count, the retired ledger in the contents list,
  the output location of the checks and the Windows command, and this
  section.
- Recorded, not changed: `requirements.txt` stays unpinned as delivered;
  the article's `U_j` are uniform on `[0,1]`, the predecessor's on
  `[-1,1]` (the article states the affine dictionary); the letters `a`,
  `T`, `K` and `J` mean different things here and in the predecessor, and
  `K` has three local meanings in this article.
