> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Atomic_Functions_Beyond_Dyadic_Report-2/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions Beyond the Critical Dyadic Case

This reproducibility package contains the English reconstruction and expansion of the attached
Rvachev atomic-functions chapter, its compiled PDF, the source OCR/scan used for reconstruction,
and deterministic numerical experiments.

## Contents

- `Atomic_Functions_Beyond_Dyadic.tex` - LaTeX report.
- `Atomic_Functions_Beyond_Dyadic.pdf` - compiled report.
- `experiments.py` - commented script generating every figure and CSV audit.
- `figures/` - vector PDF and raster PNG versions of the six figures.
- `data/` - exact/numerical validation tables.
- `source_rvachev_ocr.tex`, `source_rvachev_scan.pdf` - supplied source material.
- `requirements.txt` - Python dependencies.
- `SHA256SUMS` - checksums for the package files.

## Reproduction

From this directory:

```bash
python -m pip install -r requirements.txt
python experiments.py --output .
latexmk -pdf -interaction=nonstopmode -halt-on-error Atomic_Functions_Beyond_Dyadic.tex
```

The random experiment uses seed `20260828`.  The truncated random series has a deterministic
worst-case omitted-tail bound below `1e-12`.

## Proof-status markers in the report

- `[S]`: translated or cleanly reconstructed from the attached source.
- `[R]`: current-repository or established-literature material.
- `[N]`: proved in the report, without a priority claim.
- `[F]`: post-audit frontier formula not found in the inspected repository snapshot or focused
  literature comparison.
- `[C]`: conjecture or proposed research program.

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list (and in `SHA256SUMS` here where present), and git history archives the files. This directory keeps only figures, data, and scripts.
