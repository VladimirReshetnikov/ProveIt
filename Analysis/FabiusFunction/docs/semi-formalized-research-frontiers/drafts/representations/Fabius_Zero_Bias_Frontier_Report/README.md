# Zero-Bias Towers and Spectral Peeling in the Fabius--Rvachev System

This directory preserves and audits the report delivered in
`Fabius_Zero_Bias_Frontier_Report.zip` on 30 August 2026. The archive SHA-256
was `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`;
all 21 payload hashes in `ARRIVAL_SHA256SUMS` verified before normalization.
The report's own repository-relative novelty audit remains pinned to commit
`40fdea4cc0a728189f357389e3f114a2cb00e561`.

The mathematical manuscript develops a zero-bias hierarchy for the centered
Rvachev law and its geometric-uniform generalizations: random-index digit
replacement, iterated moment and spherical factorizations, normalized
Laguerre--Pólya derivatives, spectral peeling, an occupancy law with a
q-Pochhammer factor, compact-support Gaussianization, and phase-sensitive
endpoint asymptotics. Five further statements remain explicitly conjectural.

## Formal-status boundary

The displayed theorem labels are internal paper claims, not declarations in
the Lean library. The current corpus formalizes many inputs—the random-series
law, moments and cumulants, Fourier divisor and signs, strict shape, and
endpoint/Lambert asymptotics—but it does not yet expose a zero-bias transform,
the tower, the occupancy law, spectral-peeling hierarchy, or tower
Gaussianization. Intake therefore accepted no theorem as a new formal result
and did not change any formalization ledger. “New” means absent from the
arrival report's audited repository snapshot, not worldwide priority; general
zero-bias transformations are classical.

## Package contents

- `Zero_Bias_Towers_and_Spectral_Peeling.tex` / `.pdf` — canonical
  A4/27 mm/Libertinus source and its validated 26-page three-pass render.
- `zero_bias_tower_experiments.py` — 839-line exact/numerical experiment.
- `requirements.txt` — pinned publication environment.
- `data/` — three exact/released tables and three floating-point tables.
- `figures/` — five figures in PDF and PNG form; regenerated PDFs use
  embedded/subset TrueType outlines and no Type 3 fonts.
- `INTAKE_AUDIT.md` — provenance, replay drift, mathematical-status, and PDF
  validation record.
- `ARRIVAL_SHA256SUMS` — immutable 21-entry delivered-payload ledger.
- `SHA256SUMS` — current normalized-package ledger (excluding itself).

## Numerical replay

The publication replay used Python 3.13.14 with NumPy 2.5.2, SciPy 1.18.1,
SymPy 1.14.0, mpmath 1.3.0, and Matplotlib 3.11.1:

```bash
python -m pip install -r requirements.txt
python zero_bias_tower_experiments.py --max-level 2000 --samples 30000
```

The fixed seed is `20260830`; no network data are used. The exact moment,
collision, and released-Fourier tables reproduce the delivered bytes before
repository-required CRLF-to-LF normalization. Three floating tables differ
from arrival only by platform/library last-place rounding: the largest
absolute difference is `7.31e-14`. Figure dimensions and mathematical content
are stable; raster antialiasing and vector font encoding changed with the
pinned modern stack. See `INTAKE_AUDIT.md` for the measured comparison.

## PDF rebuild

From this directory, after deleting old auxiliaries, run exactly:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  Zero_Bias_Towers_and_Spectral_Peeling.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  Zero_Bias_Towers_and_Spectral_Peeling.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  Zero_Bias_Towers_and_Spectral_Peeling.tex
```

The final clean build used exactly those three serial passes. Its log has no
errors, undefined references, rerun requests, duplicate destinations, or
overfull boxes; five benign underfull cells in the claim-status table were
visually checked. All 39 PDF font rows are embedded and subset, Libertinus is
present, and neither the report nor its five vector figures contains Type 3
fonts. Representative theorem, plot, conjecture, and appendix pages were
rendered and inspected.
