# Upstream attribution and license scope

The machine tables and selected upstream sources are research inputs,
not newly authored results of this report. This package does not assign a
blanket license to them or change their ownership. Immutable source URLs
and hashes are recorded in `UPSTREAM.json`.

## Selected upstream files

| Packaged file | Attribution and origin |
|---|---|
| `machine/zfc_254.tm` | Mira-Cult's ZFC254 table, reproduced in `jeff87654/busy-beaver` with Jeff's Coq verification |
| `machine/zfc_253.tm` | mira-emmy's prior 253-state reduction, PR 20 of `jeff87654/busy-beaver`, built on the 254 construction |
| `Prog254.v` | Generated decoder-program source from Jeff's `ZF/m254` verification development; the decoded program derives from Mira-Cult's construction |
| `symexec.py` | Jeff's upstream Python design model for the symbolic executor |
| `tmlib.py` | Jeff's upstream table parser and sparse simulator |

These files are retained byte for byte. The upstream root and relevant
`ZF/m254` directory listings inspected at the pinned commit did not supply
a license notice for this selected material, and the selected files do
not contain an additional license grant. Consult the upstream authors and
their applicable terms for redistribution or relicensing; no license is
inferred from the repository being public.

Andrew Wade's separately licensed compiler is not a dependency of these
experiments and is not included here. Its license must not be mistakenly
treated as covering the selected Jeff/Mira source material.

## New and derived files

The following are new experiment scripts developed for this report:

- `prepare_inputs.py`
- `row_coverage.py`
- `verify_row_witnesses.py`
- `search_boot_relocation_complete.py`

The runtime table is a clearly identified transformation of the upstream
254 table. `paths.json` is reconstructed from the upstream decoder program.
The coverage certificate, search result, and verification record are
generated research data. The README and provenance notes describe the
scope and method of these experiments.

`search_boot_relocation_complete.py` adapts the upstream `symexec.py`
definitions in memory to record predecessor observations. The underlying
symbolic execution rules and register-box contracts remain upstream work;
the search itself is new. This attribution also applies to that adapted
execution.
