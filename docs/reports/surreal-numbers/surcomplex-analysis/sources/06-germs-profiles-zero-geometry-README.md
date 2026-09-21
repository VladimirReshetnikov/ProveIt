# Surcomplex Analysis
## Hahn-analytic germs, holomorphic profiles, and infinitesimal zero geometry

Article date: 21 September 2026.

## Files

- `surcomplex_analysis.pdf` — the compiled article, with a linked table of contents and references.
- `surcomplex_analysis.tex` — complete, editable LaTeX source, including the bibliography.
- `build.py` — portable three-pass pdfLaTeX build script.
- `verify_examples.py` — exact symbolic checks of the displayed finite expansions.
- `example_verification.txt` — output of the successful verification run.

## Mathematical structure

The article distinguishes local power-series germs at arbitrary points of
No(i) from coherent holomorphic Hahn-series profiles on infinitesimal
thickenings of ordinary complex domains. It proves local analytic calculus,
inverse and implicit function theorems, ramification and open-mapping results,
profile identity and Cauchy theorems, constructive Weierstrass preparation,
zero-divisor specialization, the argument principle and root-moment formulas,
biholomorphic deformation results, and additional residue and exponential
constructions. Explicit counterexamples identify hypotheses that cannot be
removed.

Hahn sums throughout the article have set-sized well-ordered support and
finite contributions at every exponent. They are not defined as sharp
limits of partial sums. Contour integrals are taken coefficientwise over
ordinary complex contours.

## Rebuilding the PDF

A TeX distribution with pdfLaTeX and the standard packages named in the
preamble is required. With Python 3.9 or later, run:

```text
python build.py
```

The script works on Windows, macOS, and Linux. It keeps intermediate files
in `_build` and places the finished PDF next to the source.

Alternatively, run the following command three times in this folder:

```text
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex
```

No external bibliography database, illustrations, or custom fonts are needed.

## Checking the worked examples

Install SymPy, then run:

```text
python -m pip install sympy
python verify_examples.py
```

The included successful run used Python 3.13.5 and SymPy 1.14.0. The script
checks all three cubic branches; a general simple-zero displacement; the
preparation and splitting of `T^2 + q exp(T)`; its first three contour moments;
a quadratic deformation inverse; and the factorial-series differential
identity through degree 24. Every check uses exact arithmetic and formal
series. None substitutes a large finite number for omega.

These finite calculations are not a machine-checked proof of the article's
general theorems. The supporting proofs, support conditions, and precise
scope are given in the article. Established foundations and related analytic
frameworks are cited; no blanket claim of literature priority is made.
