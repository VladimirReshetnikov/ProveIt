# A Convolution Calculus for Stieltjes Functions

Research continuation for Vladimir Reshetnikov's ProveIt project, 10 October 2026.

**Main article:** `Stieltjes_Convolution_Calculus.pdf` (29 pages), with the complete source in `Stieltjes_Convolution_Calculus.tex`.

The source snapshot is commit `570b0567f311cf1890865065896be2665f469e4f` of `VladimirReshetnikov/ProveIt`. The report contains analytic proofs; it is not a proof-assistant formalization. The accompanying numerical results are diagnostics, not interval certificates.

## Main results

1. Explicit, independently normalized Hadamard finite parts for products of arbitrary generalized Stieltjes functions at two shifted arguments, in both convolution orientations.
2. A finite triangular reduction to Stieltjes functions, with coefficients in ordinary zeta values and an every-index coefficient algorithm.
3. A polynomial convolution algebra for periodic Stieltjes distributions, its Bell-polynomial formula, a joint algebra including reflection, and the contact terms at the periodic singularity.
4. The exact correction between distributional differentiation and taking a raw spatial finite part, including an every-order digamma–polygamma integral.
5. Ordinary log-Gamma correlations, strict convexity, positivity of every even derivative, the optimal midpoint quadratic lower bound, and an exact convergent logarithmic cusp expansion.
6. Complete collision polynomials and sharp Hölder and Sobolev regularity for every negative-integer Hurwitz jet, with Stieltjes antiderivative specializations.
7. Strict Hankel inequalities for compensated Stieltjes parameter derivatives and a sharp fixed-dimension asymptotic with an explicit positive remainder.
8. Two precisely scoped proposed corrections to the current manuscript, plus ten further research questions.

The classical Hurwitz convolution formula and the known Dilcher series retain their attribution. The report makes no first-in-the-literature claim and does not prove the remaining short S6 or newer S8 mixed Gaussian candidate. The newer S8 candidate is distinguished from the different earlier vector already rigorously rejected in the repository.

## Files

| Path | Purpose |
|---|---|
| `Stieltjes_Convolution_Calculus.tex` | Complete standalone article source; bibliography is included directly. |
| `Stieltjes_Convolution_Calculus.pdf` | Compiled article. |
| `figures/loggamma_correlation.pdf` | Vector figure included by the TeX source. |
| `figures/loggamma_correlation.png` | Preview of the same figure. |
| `verification/exact_coefficients.py` | Exact formal coefficient checks and the table through total index four. |
| `verification/exact_jet_polynomials.py` | Exact beta-germ collision polynomial checks. |
| `verification/check_finite_parts.py` | Eleven zeroth-order finite-part checks; stable contour polylog derivatives. |
| `verification/check_reflected10.py` | Four first mixed-index checks in both orientations. |
| `verification/check_gamma_correlations.py` | Sixteen ordinary correlation checks and figure generation. |
| `verification/derivative_anomaly_check.py` | Direct raw-cutoff polygamma checks, including the first cutoff-error coefficient. |
| `verification/check_hankel_and_ladder.py` | Moment transforms, positive determinants, asymptotic bounds, and Hurwitz-ladder checks. |
| `verification/*.json` | Recorded results with parameters and precision. |
| `verification/run_all.py` | Convenient sequential runner; supports a small `--quick` smoke check. |
| `integration/proposed_corrections.patch` | Two scoped edits against the pinned source, tested on exact Git-blob bytes. |
| `integration/INTEGRATION_NOTES.md` | Placement, namespacing, source hashes, and status distinctions. |
| `sources.json` | Repository and primary-literature provenance. |
| `BUILD_AND_QA.json` | Build environment, PDF inspection, and verification summary. |
| `MANIFEST.sha256` | SHA-256 checksums of the delivered files, excluding the manifest itself. |

## Build the PDF

Use a TeX installation with `latexmk`, pdfLaTeX, Latin Modern, AMS packages, `mathtools`, `microtype`, `hyperref`, `bookmark`, `xurl`, and `fancyhdr`. These are standard TeX Live packages. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Stieltjes_Convolution_Calculus.tex
```

Equivalently, run `make pdf`. The supplied figure is already included, so Python is unnecessary just to build the article. The article was compiled with pdfTeX 1.40.25 / TeX Live 2023 and latexmk 4.83. Cross-references and citations resolve without warnings.

## Reproduce the computations

The supplied environment used Python 3.12.14, mpmath 1.3.0, SymPy 1.14.0, and Matplotlib 3.10.8. Install the recorded versions in a virtual environment if desired:

```sh
python3 -m pip install -r requirements.txt
python3 verification/run_all.py
```

The full run regenerates the result files beside the scripts and regenerates the figure. Some Stieltjes-function quadratures are deliberately high precision and may take several minutes, depending on the machine. The runner reports each completed script and fails if a child process or a numerical acceptance check fails.

A smaller smoke check takes only the two exact symbolic scripts and the quick ordinary-correlation suite:

```sh
python3 verification/run_all.py --quick
```

The quick numerical output goes to a temporary directory, preserving the supplied full numerical results and figure. The symbolic scripts regenerate their exact JSON files. Each individual script can also be run directly. The Gamma script supports `--quick`, `--dps`, `--results`, `--no-figure`, and `--figure-dir`.

The installed mpmath version showed a precision-dependent problem with default infinitesimal differentiation of a boundary polylogarithm at integer order. The final acceptance checks use finite-radius Cauchy differentiation instead; the old path is retained in one explicitly separate diagnostic. See the article for the observed error and the distinction between numerical agreement and rigorous interval certification.

## Integration

Use `integration/INTEGRATION_NOTES.md`. The patch changes only the Hurwitz-ladder domain/branch statement and the integer-relation-search wording. It is separate from adding this article. The raw finite-part convention, the distinction between ordinary and finite-part integrals, and the global Dirac terms are part of the mathematical results and should travel with any extracted formulas.

No existing repository file was changed by preparing this delivery.
