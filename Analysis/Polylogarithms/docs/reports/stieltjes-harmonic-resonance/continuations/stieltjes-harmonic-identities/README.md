# Exact Stieltjes and Harmonic Identities

**Integer dilations, three-factor products, Gamma coefficients, and corrected conjectures**  
Research continuation prepared for Vladimir Reshetnikov, 10 October 2026.

## Start here

- `article.pdf` is the complete research article.
- `article.tex`, `sections/`, and `references.tex` are its editable LaTeX sources.
- `integration/INTEGRATION_NOTES.md` maps the theorems to existing manuscript material and specific incoming research questions.
- `integration/source_audit.json` records the exact source snapshot, five incoming archives, internal paths, current S6/S8 formulas and status, and the targeted correction.
- `data/` contains completed numerical and exact symbolic diagnostics.
- `code/exact_coefficients.py` is a reusable exact symbolic coefficient generator.

The repository snapshot is `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed` from `VladimirReshetnikov/ProveIt`. This package does not modify upstream files.

## Mathematical contents

1. Complete bilinear integer-dilation reduction with arbitrary separated shifts, every Stieltjes index, exact local-scale contact polynomials, and transfer identities.
2. A self-contained generating proof of the existing unit-frequency Stieltjes closure, included as a dependency rather than presented as new.
3. Six colored Tornheim kernels for every separated triple Stieltjes finite part, an explicit three-digamma formula, and ordinary correlations of arbitrary normalized Stieltjes primitives.
4. Shifted elementary harmonic series with arbitrary convergent rational kernels, finite polygamma evaluations, antiderivatives, and all-depth principal parts and constants at the moving pole.
5. Gauss–Stieltjes subtraction for every Stieltjes order and mixed parameter jet, central-binomial examples, polylogarithmic boundary identities, and successive subtraction through every negative integer balance.
6. An all-order proof of corrected versions of Choi's printed Conjectures 4 and 6, a factor-of-two correction to formulas (41)–(46), and two harmonic-order misprints.
7. A source audit and concrete research questions, including the precise remaining tasks for the current S6 and S8 conjectures.

The identities have analytic proofs. The numerical scripts provide independent checks; they are not interval proof certificates. Exact symbolic coefficient checks also verify only their stated finite samples. No global novelty claim or proof-assistant certification is made. S6 and the current S8 remain conjectural here.

## Build the PDF

A standard TeX Live installation with pdfLaTeX and the packages listed in the preamble is sufficient. The article uses no external fonts, shell escape, network downloads, generated images, or bibliography service.

```bash
python3 code/build.py
```

This makes three LaTeX passes, checks for unresolved references and overfull boxes, and writes `article.pdf`. Intermediate TeX files go to `build/`.

You can also build directly:

```bash
pdflatex article.tex
pdflatex article.tex
pdflatex article.tex
```

## Reproduce the checks

Use Python 3.10 or later with the package versions recorded in `requirements.txt`. No network is used by the scripts.

```bash
python3 -m pip install -r requirements.txt
python3 code/run_checks.py
```

The complete run performs independent quadratures and high-precision series calculations and may take several minutes. Each component writes its own JSON in `data/`; failures return a nonzero exit code. To inspect the already completed results without recomputing:

```bash
python3 code/run_checks.py --report-only
```

Individual commands are:

```bash
python3 code/check_dilation.py
python3 code/check_harmonic.py
python3 code/check_trilinear.py --digits 32 --output data/trilinear_checks.json
python3 code/check_gauss_stieltjes.py --output data/gauss_stieltjes_checks.json
python3 code/exact_coefficients.py --output-dir data
```

`check_trilinear.py` uses 10 guard digits beyond the requested output precision. Its local finite-part computation and its Mellin/polylogarithm computation are independent. The Gauss script uses direct initial sums and Bernoulli-polynomial asymptotic tails, with a separate refinement check. The dilation script uses finite differences only for the ordinary log-Gamma comparison, as stated in the article.

## Regenerate the ZIP and checksums

```bash
python3 code/build.py --package
```

The archive contains the complete article, source, code, data, and integration material. It excludes build intermediates, Python caches, and any source repository checkout. `MANIFEST.sha256` records each included file except the manifest itself. The manifest identifies file contents, rather than claiming a bit-for-bit identical PDF across different TeX versions.

## Conventions essential to reuse

The Stieltjes expansion is

```tex
\zeta(1+s,a)=\frac1s+\sum_{m\ge0}\frac{(-1)^m\gamma_m(a)}{m!}s^m.
```

All periodic finite parts use the **right local coordinate `x-x0`** unless a different coordinate is explicitly named. Pullback of the canonical periodic distribution and the fixed-coordinate cutoff finite part differ by the stated local delta term. The triple product theorems require pairwise distinct shifts. Reciprocal Gamma factors at nonpositive integers have their entire-function meaning.

For harmonic coefficients, `E_{n,r}` is the coefficient of `y^r` in `product(1+y/k)`, while Choi's Bell polynomial `E_r(n)` equals `r! E_{n,r}`. The special `n=0` term at zero total order is retained explicitly.
