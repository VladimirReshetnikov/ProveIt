# Further Identities and Critical Transitions in the Polylogarithm–Stieltjes Calculus

Research continuation prepared for Vladimir Reshetnikov and the ProveIt project, 10 October 2026.

The report is pinned against repository commit **570b0567f311cf1890865065896be2665f469e4f**. It compares the consolidated manuscript with its newer continuation reports. The latter already prove several claims that remain conjectural in historical fragments.

## Read the article

- `polylogarithm_stieltjes_continuation.pdf` is the complete article.
- `polylogarithm_stieltjes_continuation.tex` is the complete assembled TeX source; it refers to the two included figure PDFs in `figures/`.
- `main.tex` and `article/` are the editable modular source.
- `integration/INTEGRATION.md` gives proposed placement and source actions.
- `integration/claim_ledger.json` records new, inherited, and unresolved claims explicitly.
- `integration/source_provenance.json` records pinned paths and source hashes.

## Main results

1. An exact translated Hurwitz bilinear identity, with a polylogarithmic form, all-order order derivatives, convergent endpoint expansions, and complete shift-antiderivative formulas.
2. A positive integral representation of the Gamma–trigonometric endpoint kernel. It proves positive definiteness of the endpoint-polynomial Gram matrices and shift-invariant determinant bounds for initial blocks.
3. Sharp Sobolev thresholds for normalized Stieltjes antiderivatives.
4. Three exact representations of the periodic Gamma translation energy, strict concavity, its unique half-period maximum, explicit derivatives and a definite primitive, and a geometrically convergent odd-zeta series for the first Stieltjes constant with an analytic tail bound.
5. A proof of the existing near-critical Euler conjecture `research:conj:crossing`, including its first logarithmic correction, corrected Lambert approximation, all fixed derivative-zero asymptotics, and universal profile.
6. The least eventual sign-block length for diagonal Lerch velocities: `ceil(pi/theta)+1`, in particular four at `A=2`.
7. All-order finite parts of sharp critically weighted velocity sums, including divergent contributions from both conjugate singularities.
8. A depth-preserving algebra retraction for the full Cayley shuffle ideal and its exact depth-filtered Hilbert dimensions. The frozen S6 target has a nonzero 30-term normal form of depth at most two.

“New” means proved here relative to the checked repository baseline. Classical antecedents are cited in the article; no worldwide priority claim is made for every special-case identity. The S6 and current S8 numerical period candidates remain conjectural. The formal Cayley quotient does not prove numerical independence.

## Build

The build requires `pdflatex`, `latexmk`, and the packages loaded by `article/preamble.tex`: `fontenc`, `inputenc`, `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `mathrsfs`, `microtype`, `booktabs`, `longtable`, `array`, `tabularx`, `graphicx`, `xcolor`, `enumitem`, `fancyhdr`, `url`, `hyperref`, and `cleveref`. From this directory:

```sh
python3 code/build_article.py
```

This assembles the modular source, builds the PDF in `.build/`, and copies the finished PDF to the top level. It checks for unresolved references and overflowing boxes and writes a build receipt. Rebuilding can change PDF metadata and hashes. Rendered review applies to the delivered PDF hash recorded in `verification/rendered_review.json`.

The assembled TeX can also be compiled directly, with the included `figures/` directory alongside it:

```sh
latexmk -pdf polylogarithm_stieltjes_continuation.tex
```

## Replay the checks

Python 3.10 or later is recommended. The Cayley programs use only the standard library. Other checks and plots use the dependencies in `requirements.txt`.

```sh
python3 -m pip install -r requirements.txt
python3 code/reproduce.py --suite exact
python3 code/reproduce.py --suite numeric
python3 code/reproduce.py --suite euler
```

The exact suite is quick. The numerical suites perform multiple-precision integration and long coefficient calculations and take longer. The Euler suite uses SciPy quadrature of the exact compensated density. To run its smallest diagnostic case directly:

```sh
python3 code/verify_transition.py --quick
```

The delivered Euler evidence is from the full nine-sample run; a quick replay replaces the default result file with its smaller diagnostic set. To retain the delivered receipt, supply a different `--output` path.

For figures:

```sh
python3 figures/plot_research_figures.py
```

The plot script uses the convergent Gamma series at 80 decimal digits and the exact limiting Euler profile. It produces PDF, PNG, and CSV artifacts. It does not simulate finite-epsilon Euler curves.

## Verification boundaries

The article contains the analytic proofs. The exact suite verifies 780 words, 2150 shuffle products, independent Eulerian formulas, and complete formal-ideal ranks through weight four. A separate rational computation supplies every coefficient of the frozen S6 normal form. The all-weight theorems rest on their proofs, not finite samples.

The translation checks compare ordinary quadrature with Hurwitz and polylogarithmic expressions; a supplement checks the positive kernel, endpoint Gram formula, explicit primitive, and higher derivatives. Polylogarithm order derivatives at rational shifts are evaluated through a finite Hurwitz Fourier transform, avoiding cancellation in a naive finite-difference implementation. The critical-sum checks compare independently defined velocity coefficients and the full two-singularity subtraction formulas. Euler diagnostics use the exact kernel independently of the truncated asymptotic density.

Floating-point outputs are diagnostic, not interval certificates. Analytic series tail bounds do not by themselves enclose numerical special-function evaluation error. Internal mathematical reviews are recorded, but this is not a proof-assistant formalization or an externally peer-reviewed publication.

## Integration

The package is intended as a new research continuation. It does not modify the existing repository or supersede historical artifacts silently. `integration/INTEGRATION.md` identifies the exact conjecture to promote, the two questions answered, the inherited results to retain, and the formal-versus-period distinction to preserve. The article includes thirteen further research questions with explicit obstacles and proposed approaches.

`MANIFEST.sha256` identifies the delivered content files. It excludes itself and temporary build files. Repository sources used as antecedents are referenced by pinned path and hash rather than duplicated in the package.
