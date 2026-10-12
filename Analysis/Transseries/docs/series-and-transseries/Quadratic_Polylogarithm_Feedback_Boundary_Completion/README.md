# Boundary Completion for Quadratic Polylogarithm Feedback

Research article prepared for the ProveIt project, 12 October 2026.

## Main result

For the germ `v(0)=0` defined by

\[
uv-v^2/2=\operatorname{Li}_s(r e^v),\qquad s>0,\quad u>0,
\]

the article proves the exact Taylor radius and coefficient equivalent in every parameter regime. In particular it resolves the boundary conjecture explicitly proposed in the incoming *Resonant Polylogarithm Transseries* report. The critical feedback parameter is

\[
U_c(s)^2=2\zeta(s)+\zeta(s-1)^2\qquad(s>2).
\]

The article also proves convergent critical inverse charts, finite formulas for their coefficients, every logarithmic coefficient correction at order three, a convergent joint order/feedback chart, a local complex-fold result with explicit sheet limitations, and a uniform coefficient crossover for fixed order. Ten further research questions specify what remains to be done.

The generic Lagrange, stable-law, Lambert, and singularity-analysis mechanisms are classical and have close antecedents in the repository. The claim is a completed nonlinear model, its exact constants and charts, and a resolved project conjecture. Publication priority for every model-specific formula has not been established.

## Contents

| Path | Purpose |
|---|---|
| `article.pdf` | Complete research article |
| `article.tex`, `sections/`, `references.tex` | Editable LaTeX source |
| `code/feedback_verify.py` | Exact rational checks and positive coefficient recurrence |
| `code/verify_coefficient_crossover.py` | Stable/Gaussian coefficient profiles and independent density normalization |
| `code/verify_critical_charts.py` | High-precision roots and exact symbolic logarithmic identities |
| `code/verify_crossover.py` | Critical order crossover and first exponential correction |
| `code/verify_joint_crossover.py` | Joint real crossover, physical branch checks, local complex fold |
| `code/make_figures.py` | Rebuild vector PDF and PNG figures from formulas and recorded data |
| `data/` | Complete JSON and CSV records, including finite approximation errors |
| `figures/` | Three reproducible scientific figures in PDF and PNG formats |
| `INTEGRATION.md` | Suggested location and source cross-references |
| `CLAIMS.md` | Proven results, antecedents, and precise limits |
| `provenance.json` | Pinned source snapshot, paths, hashes, primary references |
| `BUILD_VERIFICATION.json` | Build, artifact, and review checks |
| `SHA256SUMS.txt` | SHA-256 hashes of all package files other than the manifest itself |

## Rebuild the article

The checked build uses Python 3.12 and TeX Live with `latexmk` and pdfLaTeX. The LaTeX source uses ordinary packages, including `lmodern`, `mathpazo`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`, `booktabs`, `longtable`, `graphicx`, `xcolor`, `enumitem`, `fancyhdr`, `xurl`, `needspace`, `placeins`, `hyperref`, and `cleveref`.

The PDF can be rebuilt directly from the included figure PDFs:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

To rebuild the figures as well:

```bash
python3 -m pip install -r requirements.txt
make pdf
```

Equivalent commands without `make` are:

```bash
python3 code/make_figures.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Recompute the verification records

```bash
make verify
make pdf
```

Each verification program accepts `--output-dir`. To preserve the recorded release data, use a different output directory. `feedback_verify.py` and `verify_coefficient_crossover.py` also accept a comma-separated `--indices` list. The joint check accepts `--X`, `--dps`, `--complex-X`, and `--skip-complex`; its complex root diagnostic is the slowest optional part. The default input grid is documented in the scripts and JSON.

The coefficient recurrence uses NumPy `longdouble` where available. On systems where it has only binary64 range, a positive moving-scale recurrence prevents underflow. The high-precision acceptance threshold adapts to the available floating-point precision. Recorded decimal outputs need not agree bit for bit across platforms; source hashes and formulas do not depend on that agreement.

## Interpretation of verification

The first eight coefficients at `s=3,u=4` are checked in exact rational arithmetic against the original implicit equation. The symbolic logarithmic identities are exact. High-precision roots, Fourier integrals, finite coefficient ratios, and residuals are numerical diagnostics. They are not interval certificates or Lean proofs.

The order-three leading coefficient law converges slowly: at `n=2048`, the coefficient/leading ratio is approximately `0.739119713`, whereas the coefficient/second-logarithmic-refinement ratio is `1.010075657`. These data are shown rather than filtered out. Noncentral crossover ratios need not converge monotonically on the recorded grid.

The article's proofs, not the numerical residuals, establish the theorems. The focused source review did not establish a new false theorem in the inspected incoming articles. It identified an explicitly open boundary problem and supplied its proof. The integration notes retain that distinction.
