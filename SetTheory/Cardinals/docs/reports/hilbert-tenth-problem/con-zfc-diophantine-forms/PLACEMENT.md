# Placement record: batch 220 (wave 4)

Intake record, not a delivered file. The seven archives of the arrival
commit `375cc6e3d7` ("Con(ZFC) in Diophantine form (wave-4)") were extracted
straight from the committed ZIPs into numbered directories 24–30, with the
single wrapper directory removed. Nothing was edited
and nothing was run at intake.

**Wave 3 is superseded.** By Vladimir's direction the wave-4 packages
supersede the eight batch-219 packages, so directories `16-…` to
`23-…` were removed from the tree in the same commit. They remain
recoverable from placement `da064316ea` (or any commit up to the one before
this placement), whose own `PLACEMENT.md` maps their omitted members; their
archives remain in arrival `cbf94cb552`. Waves 1 and 2 were superseded
earlier; see the report README's wave table.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent *outside this report* is omitted; the
  tables below name the shortest repository path holding the same bytes.
  Wave-4 copies of wave-3 files are therefore kept, since wave 3 leaves the
  tree. Licence, notice and attribution files are always kept, wherever
  they sit in a package. The packages pin
  `ae3007ca4467011e0e051c84acb4a1dd13971b0e` (26: `a477d0fc8b`).
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

The delivered verification drivers read their vendored copies at the
delivered paths. To rerun a package, extract its archive from the arrival
commit into a scratch directory and run it there:

```sh
git show 375cc6e3d7:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `24-integer24/` | `con_zfc_synthesis_2026-10-22.zip` | 103 | 99 | 3 | 1 | `con_zfc_synthesis/` |
| `25-hybrid12/` | `con-zfc-hybrid12-2026-10-22.zip` | 72 | 70 | 1 | 1 | `con-zfc-hybrid12-2026-10-22/` |
| `26-ratio12/` | `con_zfc_synthesis_2026-10-22 (1).zip` | 112 | 105 | 2 | 5 | `con_zfc_synthesis_2026-10-22/` |
| `27-wave4/` | `ZFC_Diophantine_Wave4_Synthesis_2026-10-23.zip` | 199 | 191 | 7 | 1 | `ZFC_Diophantine_Wave4/` |
| `28-compact-norms/` | `ProveIt_ConZFC_Compact_Norms_2026-10-23.zip` | 89 | 85 | 4 | 0 | `con_zfc_synthesis/` |
| `29-simpler-forms/` | `ConZFC_Simpler_Forms_2026-10-22.zip` | 120 | 112 | 1 | 7 | `ConZFC_Simpler_Forms_2026-10-22/` |
| `30-quartic31/` | `con-zfc-nine-quartic31-ae3007c.zip` | 176 | 169 | 7 | 0 | `simpler_con_zfc_diophantine_forms/` |

Total: 871 members.

## `24-integer24/` (`con_zfc_synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/prime_padding.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `SHA256SUMS` | not staged: checksum ledger |

## `25-hybrid12/` (`con-zfc-hybrid12-2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `SHA256SUMS` | not staged: checksum ledger |

## `26-ratio12/` (`con_zfc_synthesis_2026-10-22 (1).zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/compiler/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `references/endpoint/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `verification/audit_new_circuits.log` | not staged: log file (`*.log`) |
| `verification/build24.log` | not staged: log file (`*.log`) |
| `verification/build_ratio12.log` | not staged: log file (`*.log`) |
| `verification/latex_build.log` | not staged: log file (`*.log`) |
| `verification/reproduce_coefficients.log` | not staged: log file (`*.log`) |

## `27-wave4/` (`ZFC_Diophantine_Wave4_Synthesis_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `coefficients/sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `nine/source/formal/Paper1982/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `nine/source/formal/Paper1982/NinePoly.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NinePoly.lean` |
| `nine/source/formal/Paper1982/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/source/formal/Paper1982/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `SHA256SUMS.json` | not staged: checksum ledger |

## `28-compact-norms/` (`ProveIt_ConZFC_Compact_Norms_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `vendor/inherited/K215_ordinary_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `vendor/inherited/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `vendor/inherited/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |

## `29-simpler-forms/` (`ConZFC_Simpler_Forms_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `norm12/compact_run.log` | not staged: log file (`*.log`) |
| `norm12/shifted_run.log` | not staged: log file (`*.log`) |
| `verification/SHA256SUMS` | not staged: checksum ledger |
| `verification/logs/low_degree__build_odd_scale_lifts.py.log` | not staged: log file (`*.log`) |
| `verification/logs/norm12__build_shifted_norm12.py.log` | not staged: log file (`*.log`) |
| `verification/logs/optional_materialization_in_isolated_copy.log` | not staged: log file (`*.log`) |
| `verification/logs/signed17__build_signed17.py.log` | not staged: log file (`*.log`) |

## `30-quartic31/` (`con-zfc-nine-quartic31-ae3007c.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `review/primary/Coding.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Coding.lean` |
| `review/primary/Index.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Index.lean` |
| `review/primary/Master1.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master1.lean` |
| `review/primary/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `review/primary/NinePoly.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NinePoly.lean` |
| `review/primary/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
