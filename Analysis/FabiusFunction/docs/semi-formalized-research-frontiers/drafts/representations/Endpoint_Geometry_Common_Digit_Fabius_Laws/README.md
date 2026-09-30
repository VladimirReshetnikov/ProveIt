# The Endpoint Geometry of Common-Digit Fabius Laws

Prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`article.pdf` is the complete 22-page research manuscript. Its LaTeX source
is `article.tex`. The source uses the two small generated table files included
under `generated/`; keep that folder beside the source when compiling.

## Results

The article develops a joint upper-envelope small-deviation law for the
common-digit family

    X_q = (1-q) sum_{n >= 0} q^n V_n.

It includes a three-scale expansion with an explicit linear coefficient,
marginal-standardized copula universality and its first correction,
power-ray regular variation under log-digit log-concavity, the complete
bivariate phase diagram, exact finite and continuum diagonal exponents,
optimal logarithmic parameter placement, and noncommuting Gaussian and
extreme-tail limits despite constant Pearson correlation.

The model is connected to the Fabius function at q=1/2. The source report's
open endpoint-dependence program motivates the work. This manuscript does
not claim to solve its full boundary-transseries conjecture or its
conditional-on-equality density problem.

## Proof and novelty status

The theorems have written proofs in the article. They have not been formally
verified in Lean or Rocq. The finite checks are corroborating artifacts, not
proofs of the infinite-dimensional analytic theorems. Classical ingredients
are attributed in the bibliography. Historical priority of the combined
results has not been established by an exhaustive literature search.

The sharp error estimates are for fixed parameters in strict envelope
chambers. They are not uniform under parameter coalescence, increasing
dimension, or simultaneous Gaussian/extreme scaling. The article states
those limitations explicitly and proposes eleven further research questions.

## Reproduce

The computational checks require Python 3.10 or later and only its standard
library:

```sh
python3 verify.py
```

This regenerates `verification.txt` and the files in `generated/`. It checks
804 finite envelope identities with exact rational arithmetic, one complete
finite rational probability certificate, and 100 floating-point algebraic
cancellation examples. The asymptotic tables use ordinary floating point,
not interval arithmetic. No Monte Carlo estimates are presented as proofs.

Compile the PDF with a normal TeX Live/MiKTeX installation containing
Libertinus, TikZ, tcolorbox, and the packages declared in the preamble:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The third pass is harmless and resolves any changed table-of-contents
pagination. No external bibliography processor or font download is needed.
No font files are distributed in this package.

## Files

- `article.tex`, `article.pdf`: manuscript source and compiled reading copy.
- `verify.py`: standard-library verification and table generator.
- `verification.txt`: captured output from the included program.
- `generated/exact_certificate.json`: exact certificate inputs and rational
  feasibility totals, plus approximate logarithmic evaluations.
- `generated/small_ball_bounds.csv`: asymptotic certificate table.
- `generated/bounds_table.tex`, `generated/mesh_table.tex`: table inputs.
- `SOURCE_AUDIT.md`: pinned repository source and external bibliography.

This package is a standalone contribution. No changes have been pushed to
ProveIt, and no repository-wide formal build is claimed.
