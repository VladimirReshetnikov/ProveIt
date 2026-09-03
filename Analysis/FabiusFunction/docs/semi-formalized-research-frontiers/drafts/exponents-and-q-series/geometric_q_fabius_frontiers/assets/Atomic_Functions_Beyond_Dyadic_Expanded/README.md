> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part~VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Atomic_Functions_Beyond_Dyadic_Expanded/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions Beyond the Critical Dyadic Case

This archive contains the English reconstruction and expansion of the attached Rvachev chapter.

## Build

```bash
python experiments.py --output .
latexmk -pdf -interaction=nonstopmode -halt-on-error Atomic_Functions_Beyond_Dyadic_Expanded.tex
```

The script uses the fixed seed `20260828`. All figures are written in PDF and PNG formats, and the numerical audits are written to `data/`.

## Status markers in the report

- `[S]`: translated or reconstructed source material.
- `[R]`: repository or established literature connection.
- `[N]`: proved deduction in the report, without a priority claim.
- `[F]`: post-audit frontier formula not found in the inspected repository snapshot.
- `[C]`: conjecture or research program.

> **Editorial note (2026-08-28):** the report source (.tex), compiled PDF, and the source-material copies of the Russian scan/OCR listed above were not carried into this directory: the report content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`, the scan/OCR copies are byte-identical to the previously recorded ones (same SHA-256, recorded in the volume provenance), and git history archives the absorbed archive. This directory keeps only figures, data, and scripts.
