# Geometric-Comb Interpolation, Gaussian Pascal Transforms, and the Fabius-Rvachev Boundary Layer

This archive contains the LaTeX source, rendered PDF, and reproducibility files
for a self-contained research report on Lagrange/Newton interpolation at
geometric nodes

\[
  c,\;cq,\;cq^2,\ldots,\qquad 0<q<1.
\]

The report was developed against the `main` branch of
`VladimirReshetnikov/ProveIt` at commit

```
e5175d5eb78d66f4e31db3bc506541b9bae12c57
```

as observed on 30 August 2026.  Its primary source was

```
Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/
drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/
q_pochhammer_q_binomial_monograph.tex
```

Neighboring dyadic-comb and Rvachev-Lagrange reports were used to preserve the
repository's notation and to separate imported results from new deductions.

## Contents

- `geometric_comb_q_fabius_report.tex` - complete LaTeX source.
- `geometric_comb_q_fabius_report.pdf` - rendered 65-page report.
- `geometric_comb_experiments.py` - exact-rational and high-dynamic-range
  numerical experiments, extensively commented.
- `requirements.txt` - third-party Python packages used by the experiment
  script.
- `data/lebesgue_data.csv` - endpoint and global Lebesgue diagnostics.
- `data/fabius_interpolation_data.csv` - exact-rational Fabius interpolation
  diagnostics converted to plotting fields.
- `data/identity_checks.txt` - exact identity-check transcript and selected
  Newton coefficients.
- `figures/*.pdf` - vector figures included by the LaTeX document.
- `figures/*.png` - raster copies of the same figures.

## Main mathematical results developed in the report

The report identifies the geometric Newton basis with a normalized
q-Pochhammer basis and gives explicit iterated q-difference/divided-difference
formulas.  It derives mutually inverse Gaussian-Pascal coordinate transforms,
closed Lagrange cardinals and barycentric weights, complete-homogeneous exact
residuals, Jackson-integral formulas, and an analytic infinite Newton theorem.

A sharp stability dichotomy is proved.  Evaluation at the accumulation point
has bounded Lebesgue constants,

\[
  \Lambda_n(0)=\frac{(-q;q)_n}{(q;q)_n},
\]

whereas the global Lebesgue constant satisfies

\[
  \Lambda_n^*\sim
  \frac{2(-q;q)_\infty}{e}\,\frac{q^{-\binom n2}}{n},
  \qquad \frac{x_n^*}{c}=1-\frac1n+o(n^{-1}).
\]

For the half-base Fabius comb, the report derives a reciprocal-base Gaussian
transform for the Newton coefficients, exact finite formulas, superexponential
recovery of every fixed endpoint jet, and a proved quadratic-logarithmic upper
bound for divergence inside the persistent outer gap.  It then composes the
geometric cardinal transform with the inverse-moment Appell/Rvachev synthesis
operator, producing an exact finite Lagrange-Rvachev loop and a matrix right
inverse.

Conjectural statements and open research directions are explicitly labeled as
such.

## Reproducing the experiments

Python 3.10 or later is recommended.  From the extracted archive directory:

```bash
python -m pip install -r requirements.txt
python geometric_comb_experiments.py
```

The script has no network dependency.  It overwrites the files under `data/`
and `figures/`.  Exact algebraic and Fabius computations use
`fractions.Fraction`; only the logarithmic Lebesgue maximization and plotting
use floating-point arithmetic.

A successful run ends with output of the form

```text
All exact identity checks passed.
Endpoint Lebesgue limit: 8.25598793577825006554414084943
Global asymptotic prefactor: 1.75421915716734780836138830414
```

## Rebuilding the PDF

A reasonably complete TeX Live installation with `pdflatex`, Libertinus (or the
fallback Latin Modern font), `hyperref`, `cleveref`, `mathtools`, `longtable`,
`listings`, and the standard graphics packages is sufficient.  The source
expects the vector figures to remain in `figures/`.

```bash
pdflatex geometric_comb_q_fabius_report.tex
pdflatex geometric_comb_q_fabius_report.tex
```

`latexmk -pdf geometric_comb_q_fabius_report.tex` may be used instead.
