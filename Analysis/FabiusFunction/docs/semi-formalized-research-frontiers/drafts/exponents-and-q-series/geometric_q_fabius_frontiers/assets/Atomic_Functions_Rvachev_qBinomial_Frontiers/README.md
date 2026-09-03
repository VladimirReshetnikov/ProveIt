> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Atomic_Functions_Rvachev_qBinomial_Frontiers/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions, Rvachev's up-Function, and q-Binomial Derivative Geometry

This package contains the final English reconstruction and expansion of the attached
Rvachev source material.

## Main files

- `Atomic_Functions_Rvachev_qBinomial_Frontiers.tex` - LaTeX source.
- `Atomic_Functions_Rvachev_qBinomial_Frontiers.pdf` - rendered 45-page report.
- `experiments.py` - deterministic numerical experiments and figure/data generator.
- `CORPUS_AUDIT.md` - repository pin, inherited-result boundary, and targeted
  nonduplication searches.
- `figures/` and `data/` - generated report assets and validation tables.

## Rebuild

Install the Python dependencies:

```bash
python -m pip install -r requirements.txt
```

Regenerate the numerical assets:

```bash
python experiments.py
```

Compile the report from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Rvachev_qBinomial_Frontiers.tex
```

The report uses only standard TeX Live packages and falls back from Libertinus to Latin
Modern if Libertinus is unavailable.

## Reproducibility notes

All pseudo-random experiments use fixed seeds. Exact identities are proved in the report;
the floating-point and 90-digit calculations are independent implementation checks.
`experiments.py` writes all outputs deterministically under `figures/` and `data/`.

> **Editorial note (2026-08-28):** the report source (.tex), compiled PDF, and the source-material copies listed above (scan/OCR) were not carried into this directory: the report content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`, the re-shipped copies are byte-identical to previously recorded files (SHA-256 in the volume provenance), and git history archives the absorbed archive. This directory keeps only figures, data, and scripts.
