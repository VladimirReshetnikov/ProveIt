# Sharp Conditioning Laws for Fabius and Lacunary Random Series

Research manuscript prepared for Vladimir Reshetnikov, September 28, 2026.

## Read first

`article.pdf` is the 23-page manuscript. `article.tex` is its complete LaTeX
source, with an embedded bibliography. The two figure PDFs are included, so
compiling the article does not require rerunning any computation or fetching
anything from the network.

The article proves a quantitative approximation for the entire conditioned
infinite random series, then derives sharp observation thresholds, a first
marginal correction, a Brownian bridge, exponential slack, Gumbel extremes,
and geometric-phase boundary laws. The assumptions are positive weights
satisfying `w[j+1] <= q*w[j]`, for a fixed `0 < q < 1`.

## Reading guide

- Theorem 4.2: full-configuration simplex approximation.
- Theorem 5.2: explicit first bulk-density correction, with an L1 error bound.
- Theorem 6.1: arbitrary observation masks and the sharp variance-fraction criterion.
- Theorems 7.1, 8.1, and 9.1: bridge, geometric boundary, and extreme-value laws.
- Section 10: deterministic finite-proxy calculations and direct dyadic Monte Carlo.
- Section 11: eleven proposed further research questions. (Editorial,
  2026-09-30: the qualitative part of Q7 is answered by
  `../Poisson_Extremes_Gaussian_Bridges_Small_Sum_Conditioning/`; its rates
  stay open. See the amendments below.)

## Mathematical status

These are conventional manuscript proofs, not Lean-certified theorems.
The finite-i.i.d. conditional total-variation phenomenon is classical and is
attributed to Diaconis and Freedman. The manuscript develops its extension
to infinite lacunary arrays, particularly the global coupling and simultaneous
control of bulk, tail, and slack. Worldwide priority is not established, and
no resolution of a named published open conjecture is claimed.

The ProveIt asymptotic audit was inspected, but its Lean build and axiom audit
were not rerun. The present results do not assume that all repository claims
are correct; their probability estimates are proved in the manuscript.

## Build the PDF

Use a standard TeX Live installation including newtx, microtype, the AMS
packages, and the usual graphics and hyperlink packages:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf`. The build is offline.

## Reproduce the computations

The delivered run used Python 3.11 with NumPy 2.3.5, SciPy 1.17.0, and
Matplotlib 3.10.8. The exact dependency versions are in `requirements.txt`.

```sh
python verification.py --draws 240000
```

The script uses no network access. It performs exact rational checks of the
first-correction polynomial moments, evaluates a finite simplex model using
beta/gamma distribution functions, generates both figures, and performs
importance sampling for the actual dyadic series. Seeds are recorded in the
JSON output. Run times depend on the machine.

```sh
python verification.py --skip-monte-carlo
```

This faster mode writes `data/deterministic_checks.json` and regenerates the
figures and CSV, without overwriting the stored Monte Carlo results.

### Important numerical distinction

The finite uniform-volume simplex is a proxy, not the exact conditioned
Fabius law. Its distributional formula is evaluated in floating point. The
separate importance-sampling experiment approximates the dyadic series,
keeping coordinates through `n+50`. Reported standard errors measure Monte
Carlo variability, not finite-size asymptotic error or interval-certified
bounds. Neither experiment certifies the analytic theorems.

## Files

- `article.tex`, `article.pdf`: source and finished manuscript.
- `verification.py`: executable, reproducible calculations and exact moment checks.
- `data/tv_profile.csv`: deterministic finite-simplex comparison.
- `data/verification_results.json`: full numerical run and Monte Carlo standard errors.
- `data/deterministic_checks.json`: exact moment checks and fast deterministic run.
- `figures/`: the two figures in PDF and PNG formats.
- `Makefile`, `requirements.txt`: build and dependency information.
- `source_record.json`: pinned repository and literature provenance.
- `SHA256SUMS.txt` (not kept): the delivered checksum ledger (14 entries) was
  verified in full on filing (batch 40) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`, batch 40
  row).

## Repository and literature provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot: `2cdcd74f3abcbbff7bd47c6c4265522395def609`

Primary inspected path:
`Analysis/FabiusFunction/docs/ASYMPTOTIC_COMPLETION_AUDIT.md`

References and their precise scopes are documented in the manuscript. The
scope review was targeted, not an exhaustive repository or priority audit.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). One note, after Q7 ("Point-process extremes and joint process
  limits"): its qualitative part is answered by
  `../Poisson_Extremes_Gaussian_Bridges_Small_Sum_Conditioning/` (batch 65),
  whose Theorem `thm:lacunary` proves, for every weight sequence satisfying
  `(L)`, convergence of the marked extremes to a Poisson process with
  intensity `1_[0,1](u) du e^(-z) dz`, jointly with and independent of the
  Brownian bridge and the exponential slack; the explicit rates stay open.
  One marked hygiene fix: `\hypersetup{hypertexnames=false}`, which removes
  the delivered build's duplicate destination `equation.2.1` (shared by the
  tagged display `(L)` and equation (2.1)). No label was renamed or removed.
- `figures/tv_profile.pdf`, `figures/boundary_phase.pdf`: regenerated by the
  amended program on a copy (`uv run --no-project --with numpy==2.3.5 --with
  scipy==1.17.0 --with matplotlib==3.10.8 python verification.py
  --skip-monte-carlo`) with TrueType instead of Type-3 fonts; the plotted
  data agree with `data/tv_profile.csv` to 2e-14 relative. The PNG previews,
  `data/` and the other outputs of that run are kept as delivered.
- `article.pdf`: rebuilt from the amended source and figures by three
  `pdflatex` passes (MiKTeX pdfTeX 1.40.29): 23 US Letter pages as
  delivered, no error, undefined reference, multiply defined label,
  duplicate destination, or overfull box; every font is embedded and none
  is Type 3 (the delivered PDF had three Type-3 fonts from the Matplotlib
  figures). The pages carrying the note and the figures were rendered and
  inspected.
- `verification.py`: Matplotlib's `pdf.fonttype` and `ps.fonttype` are set
  to 42. Nothing else changed: the program still writes into `data/` and
  `figures/`, so run it on a copy to keep the recorded files.
- `README.md`: the pointer under the reading guide, the retired ledger in
  the file list, and this section.
