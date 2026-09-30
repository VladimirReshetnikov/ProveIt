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

This writes `verification.txt` and `generated/` under `recomputed/` unless
`--output-root` is given (editorial amendment below; the delivered script
rewrote the recorded files, including the two table inputs, in place). It checks
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

## Editorial amendments (ProveIt, 2026-09-29)

This package was filed whole in batch 54 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`) and amended in
the editorial pass that followed. No checksum ledger was delivered.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style, and one
  note follows Corollary `cor:scalar`. For uniform digits the linear
  coefficient `D = 1/λ − 1/2 + λ^(-1) log(λ/w)`, `w = 1 − e^(−λ)`, agrees
  with the corrected expansion recorded in the editorial note under
  `conj:jet-small-ball` of `../common_digit_fabius_zonoids_frontier_report/`
  (at `m = 0`, after `X_q = (w/q) S_(0,q)`, `L = s + λ + log w`); at
  `q = 1/2` it equals `1/2 + (1 + log log 2)/log 2`, the coefficient of
  `−log x` in `fabiusWikipediaElementaryMain`, the main term of the
  machine-checked `Fabius.log_fabius_sub_explicitCorrectedWikipediaMain_isBigO`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/FabiusSharpAsymptotic.lean`).
  The article cites neither. Its own scalar error `O((log s)²)` is coarser
  than both, as it says.
- `article.tex`: the title page no longer sets a hyperref page anchor
  (`\hypersetup{pageanchor=false}` around it), because the delivered build
  reported a duplicate destination `page.1`. Both changes are marked `% ed.`.
- `article.pdf`: rebuilt with three `pdflatex -interaction=nonstopmode
  -halt-on-error article.tex` passes (MiKTeX pdfTeX): 22 pages, as
  delivered; 773,206 bytes; no error, undefined reference, rerun request,
  duplicate destination or overfull box; no Type 3 font.
- `generated/small_ball_bounds.csv`: delivered with CRLF line endings
  (Python's `csv` module) and normalized to LF on filing.
- `verify.py`: a new option `--output-root` (default `recomputed/`) receives
  `verification.txt` and `generated/`, replacing the delivered in-place
  rewrite of the recorded files and of the two tables that `article.tex`
  inputs; all outputs are UTF-8 with LF line endings and the CSV writer uses
  `lineterminator='\n'`. Changes are marked `# ed.`. Use `py verify.py` where
  `python3` does not resolve.
- Rerun on a copy (2026-09-29), `py verify.py` (Python 3.14.4, standard
  library): 804 exact tests, the finite certificate and 100 floating-point
  checks pass; all five outputs are byte-identical to the filed
  `verification.txt` and `generated/` files.
