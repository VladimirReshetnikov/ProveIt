# Uniform Coefficient Transseries across the Polylogarithmic Order-Three Resonance

**Research continuation for Vladimir Reshetnikov and the ProveIt project — 12 October 2026.**

The complete article is `article.pdf`; its main source is `article.tex` with eight modular section files and a self-contained bibliography. This package is prepared for repository integration and does not modify the source repository.

## Main results

1. An all-order coefficient expansion for quadratic polylogarithm feedback when `(s−3) log(n)/2` stays in a fixed compact real set and the positive feedback coordinate varies in a compact interval. At each fixed order the normalized error is uniform over every lattice location.
2. An exact Gamma–zeta normalization, finite Stirling-number formulas for every correction, and a parabolic-cylinder order-derivative representation. At exact resonance the scale is expressed with the lower Lambert branch; the central constants reproduce the predecessor's Gamma-moment polynomials at every order.
3. A composition theorem: after endpoint normalization and centering, every inverse-logarithmic order depends on a positive analytic outer function only through its first two endpoint derivatives.
4. Relative Gaussian/power-tail matching in growing positive windows of every fixed polynomial size in `log(n)`, with an explicit Lambert transition center and limiting profile `1 + exp(−tau)`.
5. A complete local ramification classification for real-order inverse polylogarithms, including the removable endpoints `s = 1 + 1/m`, a convergent reciprocal-order crossover chart, and an obstruction to the proposed real-order cut-modulus extension for `1 < s < 3/2`.

The article includes complete analytic proofs, explicit initial formulas, a focused source audit, and ten further research questions. `THEOREM_LEDGER.md` provides a compact statement/dependency map. `INTEGRATION.md` gives proposed repository placement and concrete status updates to prior research questions.

## Scope

The source snapshot is `VladimirReshetnikov/ProveIt` at commit
`8f5afd4d7565df808359f6a0c22f87f79a119bb9`.
The three requested directory trees and the three incoming archives at that snapshot were inventoried; the relevant integrated chapters and reports were read. Exact source paths, Git blob identifiers, and SHA-256 digests are recorded in `PROVENANCE.json`.

The proofs are conventional mathematical proofs, not Lean formalizations. No worldwide publication-priority claim is made. Classical polylogarithm expansion, Lagrange inversion, parabolic cylinder corrections, and Gaussian/power-tail competition are credited to the existing literature. The claimed continuation is the specific combined moving-order, nonlinear-feedback, all-order uniform theorem and the precisely stated local deductions.

The logarithmic coefficient expansion is asymptotic at each fixed truncation order. The scale chart and reciprocal-order inverse chart have separate proved convergence assertions. The relative growing-window result is on the positive side. The inverse endpoint classification is local and does not determine the global inverse Taylor radius.

## Contents

| Path | Purpose |
| --- | --- |
| `article.tex`, `sections/`, `references.tex` | Complete editable LaTeX article |
| `article.pdf` | Compiled article with linked contents, theorem references, and vector figures |
| `code/verify_coefficients.py` | Independent finite positive recurrences, exact rational extraction check, precision comparisons, and correction diagnostics |
| `code/verify_symbolic.py` | Exact Stirling/Gamma/marginal identities and independent Fourier quadratures |
| `code/verify_endpoints.py` | Reciprocal inverse and cut-modulus numerical diagnostics |
| `code/make_figures.py` | Recreates both vector PDF figures and PNG previews from recorded data or explicit formulas |
| `data/` | Complete numerical grid, exact identity results, environment information, and reproduction report |
| `figures/` | Vector figures plus PNG previews |
| `build.sh`, `reproduce.sh`, `requirements.txt` | Build and reproduction entry points |
| `INTEGRATION.md`, `THEOREM_LEDGER.md`, `PROVENANCE.json` | Intake guidance, proof map, and source provenance |
| `SHA256SUMS` | Digests of the delivered files, excluding this manifest itself |

## Build the PDF

Use a TeX installation containing pdfLaTeX, Latin Modern, AMS packages, `mathtools`, `microtype`, `booktabs`, `enumitem`, `fancyhdr`, `placeins`, `hyperref`, `cleveref`, and `bookmark`.

```bash
bash build.sh
```

The script uses `latexmk` when available and otherwise runs pdfLaTeX three times. It can be invoked from any working directory. The included figures allow a PDF build without running Python or downloading external material.

## Reproduce the computations

The tested environment is Python 3.12.14, NumPy 2.3.5, mpmath 1.3.0, SymPy 1.14.0, and Matplotlib 3.10.8. The recorded environment is included with the results. An isolated environment is suitable:

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
bash reproduce.sh
```

`reproduce.sh` runs all three verification programs, recreates the figures, and builds the article. Set `PROVEIT_PYTHON` to select another Python executable. Individual programs also work from an arbitrary current directory; their default output paths are resolved relative to their own source file. No checkout of ProveIt is required to run them. They read no credentials and make no network requests.

The numerical programs overwrite their corresponding files in `data/`. A reproduction may change recorded run times, environment strings, and PDF metadata. `SHA256SUMS` records the delivered package, rather than promising byte-identical output across platforms or builds.

## Verification outcomes

The packaged default runs pass the exact rational original-equation/Lagrange identity through degree eight, six Stirling identities through degree five, 36 central Gamma identities, five marginal identities through order four, and nine noninteger kernel Fourier comparisons. The coefficient experiment covers 36 cases and preserves all signed errors in CSV and JSON. At `n = 4096` the largest absolute relative error over the stated nine-case grid decreases from about 49.34% at Gaussian order to 7.03%, 2.42%, and 1.07% through orders one, two, and three.

The numerical evidence is diagnostic, not interval-certified and not a replacement for the analytic proofs. Individual asymptotic truncations need not improve monotonically. The second figure depicts the exact two-term transition expression, not independently sampled probabilities.

## Repository intake

The recommended report directory is
`Analysis/Transseries/docs/series-and-transseries/Polylogarithmic_Joint_Coefficient_Transseries/`.
Preserve the relative paths when copying this package. The proposed cross-links and research-question updates are in `INTEGRATION.md`; they have not been applied to the pinned repository.
