> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part VI** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/Rvachev_Atomic_Functions_Report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

# Atomic Functions, Rvachev's up-Function, and Smooth Cantor Splines

This archive contains the English reconstruction and research expansion of the
attached Russian chapter on atomic functions and Rvachev's `up`-function.

## Main deliverables

- `Atomic_Functions_Rvachev_Report.pdf` — rendered 28-page report.
- `Atomic_Functions_Rvachev_Report.tex` — complete LaTeX source.
- `numerical_experiments.py` — deterministic, commented numerical experiments.

The remaining PNG, CSV, and TXT files are the figures and diagnostics generated
by `numerical_experiments.py` and used by the report.

## Provenance and novelty labels

The report distinguishes four kinds of material:

1. **Source reconstruction** — translation or mathematically necessary repair
   of the attached Russian source.
2. **Repository synthesis** — material consolidated from the recursively
   audited `Analysis/FabiusFunction/docs` corpus.
3. **Derived in this report** — proofs or constructions not located in that
   audited repository snapshot; this is a corpus-relative statement, not a
   claim of priority over all mathematical literature.
4. **Conjectural frontier** — explicitly unproved conjectures and research
   programs.

The repository audit used snapshot commit
`ffd6976ec23bc99107f811e4cda2133c58cc7518`.

## Building the PDF

A recent TeX Live installation is recommended. From this directory, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Atomic_Functions_Rvachev_Report.tex
```

The source uses standard TeX Live packages, including `amsmath`, `amsthm`,
`mathtools`, `booktabs`, `longtable`, `tabularx`, `graphicx`, `microtype`,
`hyperref`, and `cleveref`.

## Reproducing the numerical experiments

Requirements:

- Python 3.10 or later
- NumPy
- SciPy
- Matplotlib

Install the Python dependencies and run:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py
```

The random-number generator has a fixed seed, so the diagnostics are
reproducible apart from ordinary floating-point and library-version variation.
The script writes all outputs beside itself.

## Included numerical outputs

- `ha_a3_density.png`
- `local_degree_distribution.png`
- `fup_clt.png`
- `ha_a3_diagnostics.csv`
- `gap_length_check_a3.csv`
- `polynomial_gap_fit_a3.csv`
- `generalized_ha_parameters.csv`
- `fup_clt_cumulants.csv`
- `local_degree_monte_carlo.txt`

> **Editorial note (2026-08-28):** the report source and compiled PDF listed above (and, where listed, the supplied source scan/OCR) were removed from this directory after their content was merged into the volume `Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance list, and Git history archives the files. This directory keeps only figures, data, and scripts.
