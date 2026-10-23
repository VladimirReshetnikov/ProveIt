# Placement record: batch 221 (wave 5)

Intake record, not a delivered file. The seven archives of the arrival
commit `b7f8b75b5b` ("Con(ZFC) in Diophantine form (wave-5)") were extracted
straight from the committed ZIPs into numbered directories 31–37, with the
single wrapper directory removed. Nothing was edited
and nothing was run at intake.

**Wave 4 is superseded.** By Vladimir's direction the wave-5 packages
supersede the seven batch-220 packages, so directories `24-…` to
`30-…` were removed from the tree in the same commit. They remain
recoverable from placement `604b1416b5` (or any commit up to the one before
this placement), whose own `PLACEMENT.md` maps their omitted members; their
archives remain in arrival `375cc6e3d7`. Waves 1 to 3 were superseded
earlier; see the report README's wave table.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent *outside this report* is omitted; the
  tables below name the shortest repository path holding the same bytes.
  Wave-5 copies of wave-4 files are therefore kept, since wave 4 leaves the
  tree. Licence, notice and attribution files are always kept, wherever
  they sit in a package. The packages pin
  `8c6eec9d19ef80538c8e61ff6e0180040583446a`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

The delivered verification drivers read their vendored copies at the
delivered paths. To rerun a package, extract its archive from the arrival
commit into a scratch directory and run it there:

```sh
git show b7f8b75b5b:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `31-sun10/` | `con_zfc_synthesis.zip` | 181 | 157 | 12 | 12 | `con_zfc_synthesis/` |
| `32-integer15/` | `con_zfc_fifteen_integer_synthesis_2026-10-22.zip` | 142 | 141 | 1 | 0 | `con_zfc_fifteen_integer_synthesis_2026-10-22/` |
| `33-signed16/` | `ConZFC_Signed16_Synthesis_2026-10-22.zip` | 101 | 96 | 5 | 0 | `con_zfc_signed16_synthesis_2026-10-22/` |
| `34-integer14/` | `con-zfc-fourteen-integer-8c6eec9d19.zip` | 288 | 280 | 8 | 0 | `con-zfc-round5/` |
| `35-cancel12/` | `con-zfc-synthesis-2026-10-22.zip` | 158 | 143 | 8 | 7 | `con-zfc-synthesis-2026-10-22/` |
| `36-small-tuple/` | `con-zfc-synthesis-2026-10-22 (1).zip` | 106 | 104 | 1 | 1 | `con-zfc-synthesis-2026-10-22/` |
| `37-wave5/` | `ZFC_Diophantine_Fourteen_Integers_2026-10-23.zip` | 221 | 208 | 11 | 2 | `ZFC_Diophantine_Wave5/` |

Total: 1197 members.

## `31-sun10/` (`con_zfc_synthesis.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `sources/NATIVE_COMPILER_README.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md` |
| `sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `sources/lean/Coding.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Coding.lean` |
| `sources/lean/Index.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Index.lean` |
| `sources/lean/Master2.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master2.lean` |
| `sources/lean/Master3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean` |
| `sources/lean/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `sources/lean/NinePoly.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NinePoly.lean` |
| `sources/lean/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `sources/lean/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `sources/lean/Theorem3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Theorem3.lean` |
| `SHA256SUMS` | not staged: checksum ledger |
| `verification/01_coefficients.log` | not staged: log file (`*.log`) |
| `verification/02_coefficients_independent.log` | not staged: log file (`*.log`) |
| `verification/03_signed10_build.log` | not staged: log file (`*.log`) |
| `verification/04_signed10_verify.log` | not staged: log file (`*.log`) |
| `verification/05_signed10_independent.log` | not staged: log file (`*.log`) |
| `verification/06_signed16_build.log` | not staged: log file (`*.log`) |
| `verification/07_signed16_verify.log` | not staged: log file (`*.log`) |
| `verification/08_signed16_independent.log` | not staged: log file (`*.log`) |
| `verification/09_positive12_build.log` | not staged: log file (`*.log`) |
| `verification/10_positive12_verify.log` | not staged: log file (`*.log`) |
| `verification/11_quartic31.log` | not staged: log file (`*.log`) |

## `32-integer15/` (`con_zfc_fifteen_integer_synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/machine/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |

## `33-signed16/` (`ConZFC_Signed16_Synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |

## `34-integer14/` (`con-zfc-fourteen-integer-8c6eec9d19.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/sources/PRIME_PADDING.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `integers/Master3.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean` |
| `integers/NineMain.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `integers/NineRatio.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `integers/NineReduce.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `integers/ProductPell.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `integers/Ratio.lean.txt` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |

## `35-cancel12/` (`con-zfc-synthesis-2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integers/upstream/Lean/Master1.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master1.lean` |
| `integers/upstream/Lean/Master2.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master2.lean` |
| `integers/upstream/Lean/Master3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean` |
| `integers/upstream/Lean/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `integers/upstream/Lean/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `sources/endpoints/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `sources/endpoints/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `verification/coefficients.log` | not staged: log file (`*.log`) |
| `verification/coefficients_independent.log` | not staged: log file (`*.log`) |
| `verification/positive_build.log` | not staged: log file (`*.log`) |
| `verification/positive_checks.log` | not staged: log file (`*.log`) |
| `verification/quartic.log` | not staged: log file (`*.log`) |
| `verification/signed_build.log` | not staged: log file (`*.log`) |
| `verification/signed_independent.log` | not staged: log file (`*.log`) |

## `36-small-tuple/` (`con-zfc-synthesis-2026-10-22 (1).zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `proofs/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `evidence/SHA256SUMS` | not staged: checksum ledger |

## `37-wave5/` (`ZFC_Diophantine_Fourteen_Integers_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `requirements.txt` | `SetTheory/Cardinals/docs/reports/quaternionic-analysis/slice-regularity-and-fueter-inversion/data/08-reflection-residue-energy-requirements.txt` |
| `signed/upstream/Master3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean` |
| `signed/upstream/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `signed/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `signed/upstream/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `signed/upstream/Packing.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Packing.lean` |
| `signed/upstream/PackingBounds.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/PackingBounds.lean` |
| `signed/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `signed/upstream/Theorem2.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Theorem2.lean` |
| `sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `nine/SHA256SUMS.json` | not staged: checksum ledger |
