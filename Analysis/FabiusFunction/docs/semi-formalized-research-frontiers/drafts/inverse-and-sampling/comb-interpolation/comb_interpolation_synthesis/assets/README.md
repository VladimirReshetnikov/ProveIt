# Companion evidence

This directory contains evidence for the canonical comb-interpolation volume;
it is not a collection of parallel manuscripts. Original report sources,
report PDFs, figure-preview PDFs, administrative READMEs, and obsolete
per-package checksum ledgers were retired after their mathematical and
provenance content was absorbed. Unique scripts, exact tables, CSV data, text
outputs, and PNG figures remain grouped by historical source slug under
`companion-evidence/`.

Treat the retained payloads as reviewed evidence. Reproduce into a disposable
copy or a separate output directory unless deliberately refreshing them.
Several packages use the same script filename, so commands below are relative
to the named source-slug directory.

## Source packages and entry points

| Source slug | Retained role | Reproduction entry point |
| --- | --- | --- |
| `Fabius_Dyadic_Comb_Sums_Report_Package` | exact dyadic comb identities and generated tables | `python dyadic_comb_experiments.py --outdir generated --max-level 8` |
| `fabius-dyadic-comb-sums-report` | exact/high-precision comb, spectral, iterated-sum, and corpus experiments | `python experiments.py --repo-docs <FabiusFunction-docs> --out <scratch-output>` |
| `fabius_dyadic_comb_report_final` | threshold, shifted-Rvachev, all-depth, and iterated-sum checks | `python fabius_dyadic_comb_experiments.py --skip-fractional` |
| `fabius_dyadic_interpolation_report` | endpoint-flat global and local interpolation checks | `python fabius_dyadic_interpolation_experiments.py --mode quick --output-dir <scratch-output>`; use `--mode report` for the longer replay |
| `fabius_interpolation_report` | broad interpolation, Hermite, derivative, Lebesgue, and figure suite | `python numerical_experiments.py --task smoke`; full orchestrator: `python reproduce_all.py --skip-existing` |
| `Fabius_Rvachev_Dyadic_Interpolation_Report` | independent global/Hermite interpolation suite | `python fabius_dyadic_interpolation_experiments.py --outdir <scratch-output> --quick` |
| `Fabius_Euler_Maclaurin_Report_Package` | exact Euler--Maclaurin, termination, Richardson, and spectral checks | `python fabius_em_experiments.py --output-dir <scratch-output> --max-power 10 --max-level 10` |
| `fabius_rvachev_exhaustion_euler_maclaurin_bundle` | exact moment, first-defect, and exhaustion verification | `python verify_fabius_rvachev_quadrature.py --max-degree 7 --output-dir <scratch-output>` |
| `fabius_ruffa_phase_calculus` | exact phase calculus and optional FFT reconstruction | `python experiments.py --output-dir <scratch-output> --grid-power 19 --skip-fft`; omit `--skip-fft` for the numerical reconstruction |
| `geometric_comb_q_fabius_report` | Gaussian-Pascal, Lebesgue, Fabius boundary, and identity checks | `python geometric_comb_experiments.py` in a disposable copy; it writes to local `data/` and `figures/` |
| `geometric_comb_interpolation_report` | moment cancellation, stability, regular variation, and exact Fabius boundary checks | `python geometric_comb_experiments.py` in a disposable copy; it writes beside the script |
| `geometric_comb_interpolation_report-3` | arbitrary-target, Fabius, Newton-growth, and reciprocal-product experiments | `python geometric_comb_experiments.py --output-dir <scratch-output>` |

`<scratch-output>` is a user-chosen directory outside the reviewed evidence
tree. `<FabiusFunction-docs>` is the checkout's
`Analysis/FabiusFunction/docs` directory.

Dependencies are package-specific. Some exact-arithmetic paths need only the
Python standard library; plotting and high-precision paths may require
`mpmath`, Matplotlib, NumPy, SciPy, or SymPy. The retained requirements files
are historical minimum-version notes rather than a unified, locked
environment.

## Shared payload

`companion-evidence/shared/requirements-mpmath-matplotlib.txt` represents the
only byte-identical payload pair in the source inventory. It replaces the two
identical `requirements.txt` files formerly carried by
`fabius_interpolation_report` and
`Fabius_Rvachev_Dyadic_Interpolation_Report`; both source rows remain visible
in `../source_disposition.csv`.

## Audit records

- [`HISTORICAL_LEDGER_AUDIT.csv`](HISTORICAL_LEDGER_AUDIT.csv) classifies all
  151 rows from eight historical package ledgers at the immutable source pin.
- [`VALIDATION.md`](VALIDATION.md) separates completed source/evidence checks
  from pending canonical-publication checks.
- `COMPANION_PAYLOADS.csv` and `SHA256SUMS`, when present, are the canonical
  destination map and live checksum ledger. They must not be confused with
  the historical ledgers.

The source pin is
`73f0b373126ef22a3b5dccadfa7b99d61d445345`. Git history is the archive for
retired manuscript and preview files.
