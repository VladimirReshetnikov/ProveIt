# Reproducibility assets

This directory is the reproducibility companion to the consolidated
`q-Series and Inverse q-Analogs` volume.  It preserves the
distinct computational experiments that accompanied the six source reports
without preserving six parallel report bundles.

The mathematical status is deliberately strict:

- the canonical LaTeX volume contains the statements and human-readable
  proofs;
- the programs, tables, logs, and figures here provide reproducible
  calculations, diagnostics, and illustrations;
- exact symbolic assertions in a program are useful checks, but the
  computations are evidence rather than proof; and
- decimal agreement, plots, and asymptotic residuals never upgrade a claim to
  theorem status.

`ASSET_DISPOSITION.csv` is the immutable path-by-path migration and retirement
record.  Its source paths are historical paths formerly relative to the
surrounding `exponents-and-q-series/` directory, and destination paths are
relative to the canonical `q_pochhammer_q_binomial_monograph/` directory.  Its 73
tracked source hashes are frozen against asset snapshot
`f46e5d7f6f225bf0a43d8945e67d6f0e4aec8d54`, where all 73 match.  This is
distinct from `../audit/SOURCE_REVISION` at
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`, which pins the normalized
six-package inputs for the theorem/source-concordance audit and matches only 66
of the 73 asset rows.  The inventory has 77 rows: 73 tracked source files plus
four ignored TeX-build paths that were absent untracked transients at the
retirement freeze.  Every tracked row records its source SHA-256, every one of
the 39 migrations records its canonical SHA-256, and the other 38 rows carry
`NOT_RETAINED`.  The four absent paths carry `UNTRACKED_TRANSIENT_ABSENT`.  The
retained set consists of six
programs, 19 computational outputs, and 14 vector figures.  The retirements
cover superseded reports, duplicate renderings, package metadata, and build
byproducts.  No content-based deletion was inferred merely from a similar
filename.

| Disposition | Asset class | Count |
| --- | --- | ---: |
| Retain | Python programs | 6 |
| Retain | CSV/TXT computational outputs | 19 |
| Retain | Vector PDF figures | 14 |
| Retire | Superseded report PDFs | 6 |
| Retire | Redundant PNG previews | 6 |
| Retire | Source-package READMEs | 6 |
| Retire | Source-package checksum ledgers | 6 |
| Retire | Source requirements files | 2 |
| Retire | Superseded report TeX sources | 6 |
| Retire | Generated numerical TeX fragments | 2 |
| Retire | Ignored TeX build byproducts | 4 |
|  | **Total** | **77** |

## Retained layout

Each experiment remains an independent, self-contained calculation.  The
repository-wide convention places executable programs in `scripts/`, while
the experiment root owns sibling `data/`, `figures/`, and `output/`
directories:

```text
assets/
├── README.md
├── VALIDATION.md
├── requirements.txt
├── ASSET_DISPOSITION.csv
└── experiments/
    ├── functions/
    │   ├── scripts/
    │   ├── figures/
    │   └── output/
    ├── jet_atlas/
    │   ├── scripts/
    │   └── output/
    ├── extended/
    │   ├── scripts/
    │   ├── data/
    │   ├── figures/
    │   └── output/
    ├── branch_geometry/
    │   ├── scripts/
    │   ├── data/
    │   └── figures/
    ├── compact/
    │   ├── scripts/
    │   └── output/
    └── forward/
        ├── scripts/
        └── output/
```

The names identify provenance lanes, not mathematical priority:

| Lane | Source package | Computational emphasis |
| --- | --- | --- |
| `functions` | `inverse_q_analog_functions_report/` | Branch atlases, log-periodic correction, q-gamma branches, and representative inverse checks. |
| `jet_atlas` | `inverse_q_analog_jet_atlas/` | Exact inverse jets, cyclotomic multiplicities, double scaling, and high-precision residual tests. |
| `extended` | `inverse_q_analogs_extended_report/` | q=-1 critical geometry, radial inverses, q-gamma regimes, and Fabius/Rvachev parameter recovery. |
| `branch_geometry` | `inverse_q_analogs_report/` | Critical-value collisions, discriminants, branch continuation, and accuracy diagnostics. |
| `compact` | `inverse_q_analogs_report-2/` | Compact symbolic and high-precision cross-check suite. |
| `forward` | `q_pochhammer_q_binomial_expansions_report/` | Forward q-Pochhammer, Gaussian, root-of-unity, and double-scaling expansion checks. |

All CSV files are retained in `data/`.  The two branch-geometry text files
remain in `data/` as well because they are part of that program's established
`DATA` contract.  Source-root audit logs move to `output/`.  Only vector PDF
figures are retained; the extended experiment's six PNG files are preview
renderings of those vector figures.  The 14 retained PDFs are historical
Matplotlib artifacts and contain embedded/subset Type 3 DejaVu glyphs.  They
are not input by the canonical manuscript; its separate publication gate
requires Libertinus prose, Type-1 fonts, and no Type 3 fonts.

## Environment

Python 3.10 or later is recommended.  From this `assets/` directory:

```console
python -m venv .venv
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
```

Activate the virtual environment in the usual platform-specific way before
running the commands below.  The consolidated dependency floors are the
componentwise maxima required by the six programs:

- `mpmath>=1.3`
- `sympy>=1.14`
- `numpy>=2.0`
- `matplotlib>=3.8`

The programs use no network data, randomness, or repository-local Python
packages.  They intentionally keep their original precisions: 80 decimal
digits except for the 60-digit branch-geometry suite.

## Running the experiments

Run each command from the named experiment root.  This makes the destination
of every generated file explicit and prevents one experiment from overwriting
another lane's identically named output.

### Functions

```console
cd experiments/functions
python scripts/inverse_q_analogs_experiments.py
```

The program refreshes `output/numerical_results.txt`, prints that log to
standard output, and regenerates these vector figures:
`figures/finite_pochhammer_branch_atlas.pdf`,
`figures/log_periodic_correction.pdf`, and
`figures/qgamma_inverse_branches.pdf`.  It also emits a report-specific
`numerical_results.tex` fragment; that fragment is a disposable byproduct and
is not part of the canonical asset set.

### Inverse-jet atlas

```console
cd experiments/jet_atlas
python scripts/inverse_q_analog_experiments.py \
  --digits 80 --output output/numerical_checks.txt
```

The program overwrites the named audit log and reports its path on standard
output.  `--digits` may be increased, but values below 40 are rejected because
the residual checks become unstable.

### Extended experiment

```console
cd experiments/extended
python scripts/inverse_q_analogs_experiments.py --output .
```

The program refreshes seven CSV files in `data/`,
`output/numerical_summary.txt`, and six vector figures in `figures/`.  The
original program also generates six PNG previews and a report-only
`numerical_results.tex` fragment.  Those reproducible byproducts are
intentionally uncommitted: the PDFs are the canonical figures, and the
consolidated volume no longer inputs the generated fragment.

### Branch geometry

```console
cd experiments/branch_geometry
python scripts/numerical_experiments.py
```

The program refreshes five CSV tables, `data/secondary_discriminants.txt`, and
`data/summary.txt`, then regenerates five vector figures in `figures/`.  It
prints the experiment root and the computed `n=5` collision parameter.

### Compact cross-checks

```console
cd experiments/compact
python scripts/inverse_q_analogs_experiments.py
```

The program overwrites `output/numerical_results.txt` and writes the identical
text to standard output.

### Forward expansions

```console
cd experiments/forward
python scripts/q_expansion_experiments.py
```

This program writes its complete audit to standard output and does not create
a file itself.  To refresh the retained snapshot in a POSIX-compatible shell,
capture that stream explicitly:

```console
python scripts/q_expansion_experiments.py > output/numerical_results.txt
```

The exact q=1 and q=-1 suites each check all 230 pairs
`0 <= k <= n <= 20` before the numerical asymptotic tests are printed.

## Migrated path adjustment

The source programs were originally beside their outputs.  Moving them into
`scripts/` changes the meaning of `Path(__file__).parent` (or
`Path(__file__).with_name(...)`).  The migrated copies of the `functions`,
`jet_atlas`, `extended`, `branch_geometry`, and `compact` programs therefore
make a small, mechanical path adjustment: they compute the experiment root as
the parent of `scripts/` and route existing outputs to the sibling directories
shown above.  The `forward` program only writes to standard output and needs
no path rewrite.  These edits do not change the mathematics, default
precision, row order, or displayed values.  Text and CSV writers also use
explicit LF line endings so that retained audit logs are reproducible across
Windows and POSIX hosts.

The source copies remained untouched through the hash freeze and were then
retired together.  `VALIDATION.md` records the clean-room rerun of every
migrated program and distinguishes byte-for-byte reproduction from harmless
rendering metadata and last-digit floating-point drift.

## What is not retained

The six old report PDFs and LaTeX manuscripts are superseded by the single
canonical volume.  Their mathematical provenance lives in the theorem
concordance rather than in six competing renderings. Source READMEs were
absorbed here; source checksum ledgers were retired after their historical
receipts were recorded; the two source requirements files were replaced by the
single requirements file above; generated LaTeX table fragments and TeX
`.aux`, `.log`, `.out`, and `.toc` files are build products; and PNG previews
are unnecessary when the corresponding vector PDFs are present.

Retirement does not erase history: every old package remains recoverable from
repository snapshot `f46e5d7f6f225bf0a43d8945e67d6f0e4aec8d54`.
Package checksum manifests are retired. Source and canonical-destination
digests in `ASSET_DISPOSITION.csv`, together with pinned repository history,
preserve migration receipts without creating a live checksum gate.
