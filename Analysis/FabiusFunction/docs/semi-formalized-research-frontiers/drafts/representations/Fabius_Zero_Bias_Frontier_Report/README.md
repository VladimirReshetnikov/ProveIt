# Zero-Bias Towers and Spectral Peeling in the Fabius--Rvachev System

This directory preserves and audits the report delivered in
`Fabius_Zero_Bias_Frontier_Report.zip` on 30 August 2026. The archive SHA-256
was `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`;
all 21 hashes in the submitted arrival ledger verified before normalization.
That ledger, formerly filed as `ARRIVAL_SHA256SUMS`, is now retired and
recoverable from Git history.
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

- `Zero_Bias_Towers_and_Spectral_Peeling.tex` — current 1,926-line,
  72,231-byte A4/27 mm/Libertinus source; SHA-256
  `5b0eb2cf61123d5c9a6bd7ec5fdef5f7f09b2130ea02e3437d54f6dac2e27e42`.
- `Zero_Bias_Towers_and_Spectral_Peeling.pdf` — retained validated 26-page
  three-pass render of the preceding frozen source checkpoint; SHA-256
  `e7698059db2a24985b90258683af4fde277235159379fc7b294583dbb6bf0f37`.
  It is not a rendering of the current live source; a rebuild is pending.
- `zero_bias_tower_experiments.py` — 839-line exact/numerical experiment.
- `requirements.txt` — pinned publication environment.
- `data/` — three exact/released tables and three floating-point tables.
- `figures/` — five figures in PDF and PNG form; regenerated PDFs use
  embedded/subset TrueType outlines and no Type 3 fonts.
- `INTAKE_AUDIT.md` — immutable provenance, replay drift, mathematical-status,
  and 2026-08-31 synchronized-source/PDF validation record. That record
  predates the current source-only notation edit.
- The former 21-entry arrival and normalized-package ledgers are retired;
  their validated checkpoint bytes remain recoverable from Git history.

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

The retained PDF's final clean build on 2026-08-31 used exactly those three
serial passes from clean auxiliaries, producing 25, 26, and 26 pages from the
then-current 1,926-line, 72,171-byte source with SHA-256
`80b3d01e7555d322781fedf671f1984279cb8e997d964f96942cb117db79b9b2`.
The live source identified above is 60 bytes newer and has not been rebuilt;
the following observations apply only to the retained PDF checkpoint. Its
final build log has no
errors, undefined references, rerun requests, duplicate destinations, or
overfull boxes; five benign underfull cells in the claim-status table were
visually checked. All 26 pages are A4, rotation zero, and nonblank. All 39 PDF
font rows are embedded and subset, five are Libertinus, and neither the report
nor its five vector figures contains Type 3 fonts. Title, author, subject, and
keywords metadata are present. Physical pages 1, 13, 18--20, 22, and 26 were
visually checked, including all five figures and the repaired running heads.
The former exhaustive mixed current-source/retained-artifact ledger passed in
full at its recorded checkpoint; it is now retired and recoverable from Git
history. That verification did not assert source/PDF rendering parity.
