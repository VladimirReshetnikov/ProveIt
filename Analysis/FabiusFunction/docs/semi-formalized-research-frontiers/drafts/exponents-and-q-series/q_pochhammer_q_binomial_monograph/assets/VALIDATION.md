# Reproducibility validation

This receipt records the clean-room validation of the consolidated inverse
q-analog experiment archive on 2026-08-31.  The validation is evidentiary: it
checks that the migrated programs still perform their original calculations,
but it is not substituted for any proof in the canonical manuscript.

## Environment and method

The six programs were run serially, each from its experiment root, in a fresh
Python 3.14.4 virtual environment containing:

```text
mpmath       1.3.0
sympy        1.14.0
numpy        2.5.2
matplotlib   3.11.1
```

The environment was outside the repository.  No program downloads data, uses
randomness, or imports a repository-local Python package.  Before execution,
all six migrated scripts were parsed with Python's `ast` module.  After the
runs, the 33 retained non-script files were restored from the source packages
and compared by SHA-256; all 33 comparisons were exact.  Consequently the
repository preserves the historical numerical snapshots and vector figures,
while the reruns below test the migrated path logic and calculations.

## Serial rerun results

| Lane | Command from the lane root | Result |
| --- | --- | --- |
| `functions` | `python scripts/inverse_q_analogs_experiments.py` | Exit 0.  The numerical log reproduced byte-for-byte after deterministic LF output was enabled.  All three vector figures regenerated successfully. |
| `jet_atlas` | `python scripts/inverse_q_analog_experiments.py --digits 80 --output output/numerical_checks.txt` | Exit 0.  The audit log reproduced byte-for-byte; its SHA-256 was `bf694b83bddb99563fb4e51e823e31e4596d2538c5ec2e0eb17f0f5bcda85f73`. |
| `extended` | `python scripts/inverse_q_analogs_experiments.py --output .` | Exit 0 and 94 rows.  Six of seven CSV files and the human-readable summary reproduced byte-for-byte; all six PDF figures regenerated.  The sole numerical drift is detailed below. |
| `branch_geometry` | `python scripts/numerical_experiments.py` | Exit 0.  All seven retained CSV/TXT outputs reproduced byte-for-byte, all five PDF figures regenerated, and the reported n=5 collision parameter was `0.84015337830837665866293643188913294310139258365832`. |
| `compact` | `python scripts/inverse_q_analogs_experiments.py` | Exit 0.  The audit log reproduced byte-for-byte; its SHA-256 was `5c6051cf8192a73fd099c40dfcd9336bc42d15284b85151d2064ef5565a95f1e`. |
| `forward` | `python scripts/q_expansion_experiments.py` | Exit 0.  Captured standard output reproduced the retained audit text exactly after platform line-ending normalization; the retained file's SHA-256 was `a2052f71be8ca67e6728c522377d34284dc03691cdc1376b0f5cf053ec5099eb`. |

The regenerated PDFs were produced as nonempty files but did not have stable
hashes under Matplotlib 3.11.1: PDF creation timestamps, producer
metadata, font subset identifiers, and rendering-version details are allowed
to vary.  The canonical archive therefore retains the 14 original vector PDFs
byte-for-byte.  PNG previews are intentionally omitted because the PDFs are
the authoritative vector artifacts.  Those historical Matplotlib PDFs contain
embedded/subset Type 3 DejaVu glyphs; the consolidated manuscript does not
input them, and its independent publication audit requires no Type 3 font.

## The one floating-point difference

`extended/data/radial_inverse.csv` is the only generated text file that was
not byte-identical under the newer NumPy/Python runtime.  Four of its rows
differ, and only in the last one to three units at the seventeenth through
twenty-first printed decimal places.  Two rows inherit the grid value
`0.02050757654370109` rather than `0.02050757654370108`; the corresponding
high-precision approximations move by about `3e-18`.  Two other approximations
move by about `2e-18`.  Every printed relative-error column is identical.
These are binary floating-point grid-construction differences, not a change in
the formula, branch, precision, or claimed asymptotic behavior.  The canonical
archive retains the historical CSV exactly, and this receipt makes the runtime
dependence explicit.

## Inventory checks

`ASSET_DISPOSITION.csv` has 77 rows: 39 migrations and 38 retirements.  The
retained set consists of six Python programs, 19 CSV/TXT outputs, and 14 vector
PDF figures.  No generated TeX fragment, PNG preview, source-package checksum
ledger, report rendering, or TeX build byproduct is present in the canonical
experiment tree.  Before source retirement, the disposition ledger was frozen
with 73 source SHA-256 values, four explicit
`UNTRACKED_TRANSIENT_ABSENT` markers, 39 canonical destination SHA-256 values,
and 38 `NOT_RETAINED` markers.  All 39 destination hashes verified, and all 33
non-script migrations were byte-identical to their sources. The six source
directories were then retired; snapshot
`f46e5d7f6f225bf0a43d8945e67d6f0e4aec8d54` preserves them. Package checksum
manifests are retired; source and destination digests in
`ASSET_DISPOSITION.csv` preserve the migration receipts without acting as a
live package gate.
