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

## Placement record: batch 222 (wave 6)

Intake record, not a delivered file. The eight archives of the arrival
commit `29ca562f8f` ("Con(ZFC) in Diophantine form (wave-6)") were extracted
straight from the committed ZIPs into numbered directories 38–45, with the
single wrapper directory removed. Nothing was edited and nothing was run at
intake.

**Wave 5 is kept.** By Vladimir's direction, wave 6 is placed beside wave 5
(sources 31–37), not instead of it; this section is appended to the
batch-221 record above. The report had moved from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/` to
`Computability/DiophantineConsistency/` in `ea8ae71167`, after the packages'
pin.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 files of this report, which stay in the tree. The tables below
  name the shortest repository path holding the same bytes. Licence, notice
  and attribution files are always kept. All eight packages pin
  `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

To rerun a package, extract its archive from the arrival commit into a
scratch directory and run it there:

```sh
git show 29ca562f8f:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `38-batching11/` | `con-zfc-quadratic-batching-2026-10-23.zip` | 115 | 86 | 29 | 0 | `con-zfc-quadratic-batching/` |
| `39-direct10/` | `ConZFC_Direct_Quadratic10_2026-10-23.zip` | 148 | 86 | 62 | 0 | `con-zfc-direct-quadratic10/` |
| `40-packing10/` | `ConZFC_Quadratic_Packing_2026-10-23.zip` | 81 | 54 | 27 | 0 | `38-quadratic-packing/` |
| `41-bose-chowla/` | `ConZFC_BoseChowla_2026-10-23.zip` | 82 | 42 | 40 | 0 | `con-zfc-bose-chowla/` |
| `42-additive-b4/` | `ConZFC_Additive_Coding_2026-10-23.zip` | 144 | 122 | 22 | 0 | `con-zfc-additive-coding/` |
| `43-sidon10/` | `con-zfc-b2-2026-10-23.zip` | 109 | 51 | 58 | 0 | `con-zfc-b2-2026-10-23/` |
| `44-b4-sparse/` | `ZFC_Diophantine_B4_Sparse_Encodings_2026-10-23.zip` | 226 | 144 | 79 | 3 | `ZFC_Diophantine_B4_Sparse_Encodings/` |
| `45-multioutput/` | `con-zfc-multioutput-22e75dd6b8.zip` | 244 | 188 | 54 | 2 | `con-zfc-multioutput-22e75dd6b8/` |

Total: 1149 members.

### `38-batching11/` (`con-zfc-quadratic-batching-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `compiler/source_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `compiler/source_proofs/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `compiler/source_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `compiler/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `compiler/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `compiler/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `compiler/source_proofs/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `compiler/source_proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `compiler/source_proofs/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `compiler/source_proofs/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `compiler/source_proofs/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `compiler/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `eleven/source_proofs/SHARP12_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/positive.tex` |
| `nine/inherited/Carries.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Carries.lean` |
| `nine/inherited/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/inherited/PACKAGE37_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/PROOF.md` |
| `nine/inherited/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `nine/parent31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `provenance/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `provenance/k215.native.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm` |
| `provenance/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `signed10/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `signed10/generated/norm3_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm3_polynomial.json` |
| `signed10/inherited/INDEPENDENT_MATHEMATICAL_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` |
| `signed10/inherited/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed10/inherited/SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `signed10/inherited/build_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `signed10/inherited/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |

### `39-direct10/` (`ConZFC_Direct_Quadratic10_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `data/upstream_coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `optional_compact/code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `optional_compact/coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `optional_compact/coefficients/upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `optional_compact/coefficients/upstream/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `optional_compact/coefficients/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `optional_compact/coefficients/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `optional_compact/coefficients/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `optional_compact/coefficients/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `optional_compact/coefficients/upstream/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `optional_compact/coefficients/upstream/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `optional_compact/coefficients/upstream/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `optional_compact/coefficients/upstream/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `optional_compact/coefficients/upstream/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `optional_compact/coefficients/upstream/package36_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `optional_compact/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `optional_compact/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `optional_compact/upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `optional_compact/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `optional_compact/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `optional_compact/upstream/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `optional_compact/upstream/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `optional_compact/upstream/package31_build_signed10.py.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `optional_compact/upstream/package31_signed10.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/signed10.json` |
| `optional_compact/upstream/signed10_INDEPENDENT_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_AUDIT.md` |
| `optional_compact/upstream/signed10_INDEPENDENT_MATHEMATICAL_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` |
| `optional_compact/upstream/signed10_SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `optional_compact/upstream/signed10_SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/package31_build_signed10.py.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `upstream/package31_signed10.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/signed10.json` |
| `upstream/signed10_INDEPENDENT_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_AUDIT.md` |
| `upstream/signed10_INDEPENDENT_MATHEMATICAL_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` |
| `upstream/signed10_SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `upstream/signed10_SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `verification/coefficients_rebuild.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |

### `40-packing10/` (`ConZFC_Quadratic_Packing_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `research_candidate/UPSTREAM_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `research_candidate/UPSTREAM_COEFFICIENT_SOURCES.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/SOURCES.json` |
| `research_candidate/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `research_candidate/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `research_candidate/source_proofs__package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `upstream/COEFFICIENT_BINDING_AT_PIN.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `upstream/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/NATIVE_STREAM_README.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md` |
| `upstream/PARENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |

### `41-bose-chowla/` (`ConZFC_BoseChowla_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `generated/norm3_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm3_polynomial.json` |
| `generated/norm4_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm4_polynomial.json` |
| `upstream/dependencies/24-POSITIVE_AND_PELL_SATURATION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/positive/upstream/sections_positive.tex` |
| `upstream/dependencies/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `upstream/dependencies/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `upstream/dependencies/34-INHERITED_POSITIVE12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/positive12/upstream/POSITIVE12_PROOF.md` |
| `upstream/dependencies/34-SHIFTED12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/positive/SHIFTED12_PROOF.md` |
| `upstream/dependencies/34-synthesis_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/report/synthesis_report.tex` |
| `upstream/dependencies/37-POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/PROOF.md` |
| `upstream/dependencies/37-positive_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/section.tex` |
| `upstream/dependencies/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `upstream/dependencies/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/dependencies/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/dependencies/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/dependencies/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/dependencies/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/dependencies/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `upstream/dependencies/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `upstream/dependencies/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `upstream/source31/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `upstream/source31/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/source31/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `upstream/source31/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream/source31/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream/source31/signed10/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `upstream/source31/signed10/audit_signed10_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/audit_signed10_independent.py` |
| `upstream/source31/signed10/build_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `upstream/source31/signed10/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `upstream/source31/signed10/data/INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/INSTANCE.json` |
| `upstream/source31/signed10/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `upstream/source31/signed10/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `upstream/source31/signed10/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `upstream/source31/signed10/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `upstream/source31/signed10/data/beta_sun.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta_sun.bin.gz` |
| `upstream/source31/signed10/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `upstream/source31/signed10/data/constants.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/constants.json` |
| `upstream/source31/signed10/data/index_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/index_bound.json` |
| `upstream/source31/signed10/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `upstream/source31/signed10/verify_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/verify_signed10.py` |

### `42-additive-b4/` (`ConZFC_Additive_Coding_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficient_backend/proofs/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `coefficient_backend/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/wang943_tiles.json` |
| `sources/31-sun10/sources/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `sources/KEndpoint215.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/KEndpoint215.lean` |
| `ten_integer/SOURCE_PINS.upstream31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/SOURCE_PINS.json` |
| `ten_integer/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `ten_integer/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `ten_integer/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `ten_integer/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `ten_integer/data/beta_sun.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta_sun.bin.gz` |
| `ten_integer/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `ten_integer/data/index_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/index_bound.json` |
| `ten_integer/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `ten_integer/data/upstream_INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/INSTANCE.json` |
| `ten_integer/generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `ten_integer/generated/norm3_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm3_polynomial.json` |
| `ten_integer/generated/norm4_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm4_polynomial.json` |
| `ten_integer_composed/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `ten_integer_composed/generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `ten_integer_composed/generated/norm3_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm3_polynomial.json` |
| `ten_integer_composed/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `ten_integer_composed/source_proofs/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |

### `43-sidon10/` (`con-zfc-b2-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `vendor/compiler/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `vendor/compiler/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `vendor/compiler/pell/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `vendor/compiler/pell/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `vendor/compiler/pell/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `vendor/compiler/pell/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `vendor/compiler/pell/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `vendor/compiler/pell/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `vendor/compiler/pell/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `vendor/compiler/pell/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `vendor/compiler/pell/pell_fixed_affine_exponent52.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` |
| `vendor/compiler/pell/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `vendor/machine/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `vendor/machine/README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `vendor/machine/canonicalization.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/canonicalization.json` |
| `vendor/machine/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `vendor/machine/proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `vendor/machine/provenance.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/provenance.json` |
| `vendor/package18/COEFFICIENT_BINDINGS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/integer15/upstream/COEFFICIENT_BINDINGS.json` |
| `vendor/package31/INSTANCE_BINDINGS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/INSTANCE_BINDINGS.json` |
| `vendor/package31/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/SOURCE_PINS.json` |
| `vendor/package31/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `vendor/package31/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `vendor/package31/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `vendor/package31/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `vendor/package31/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `vendor/package31/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `vendor/package31/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `vendor/package31/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `vendor/package31/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `vendor/package31/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `vendor/package31/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `vendor/package31/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `vendor/package31/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `vendor/package31/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `vendor/package31/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `vendor/package31/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `vendor/package31/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` |
| `vendor/package31/signed10/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `vendor/package31/signed10/SOURCES.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SOURCES.json` |
| `vendor/package31/signed10/build_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `vendor/package31/signed10/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `vendor/package31/sources/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `vendor/package31/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` |
| `vendor/package31/sources/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `vendor/package31/sources/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `vendor/package31/sources/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `vendor/package31/sources/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `vendor/package31/sources/SIGNED17_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/signed17_proof.md` |
| `vendor/quartic31-source/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `vendor/quartic31-source/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/upstream/arithmetic/SOURCE_LEDGER.json` |
| `vendor/quartic31-source/build_arithmetic.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/upstream/arithmetic/build_arithmetic.py` |
| `vendor/quartic31-source/upstream/quartic32.pinned.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/integer15/upstream/base/quartic32.upstream.json` |

### `44-b4-sparse/` (`ZFC_Diophantine_B4_Sparse_Encodings_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `nine/generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `positive/upstream/30-POSITIVE12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/positive/upstream/POSITIVE12_PROOF.md` |
| `positive/upstream/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/upstream/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `quartic/sources/31-sun10__quartic31__QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `quartic/sources/31-sun10__quartic31__quartic31_sos125.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_sos125.json` |
| `quartic/sources/31-sun10__quartic31__quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `quartic/sources/31-sun10__quartic31__upstream__30-quartic31__arithmetic__QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `quartic/sources/31-sun10__quartic31__upstream__30-quartic31__arithmetic__build_arithmetic.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/upstream/arithmetic/build_arithmetic.py` |
| `quartic/sources/31-sun10__quartic31__upstream__quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `quartic/sources/31-sun10__sources__ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `quartic/sources/34-integer14__low_degree__QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `quartic/sources/34-integer14__nine__QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `quartic/sources/37-wave5__lowdegree__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/PROOF.md` |
| `quartic/sources/37-wave5__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/PROOF.md` |
| `quartic/sources/37-wave5__signed__SIGNED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/SIGNED_PROOF.md` |
| `review/31-sun10_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `review/32-integer15_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/README.md` |
| `review/33-signed16_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/README.md` |
| `review/34-integer14_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/README.md` |
| `review/35-cancel12_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/README.md` |
| `review/36-small-tuple_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/README.md` |
| `review/37-wave5_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/README.md` |
| `review/37-wave5_nine_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/PROOF.md` |
| `signed_audit/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `signed_audit/generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `signed_audit/upstream/33-signed16__README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/README.md` |
| `signed_audit/upstream/33-signed16__report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/report.tex` |
| `signed_audit/upstream/34-integer14__README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/README.md` |
| `signed_audit/upstream/34-integer14__SIGNED_FAMILY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/integers/SIGNED_FAMILY_PROOF.md` |
| `signed_audit/upstream/34-integer14__audit__COFINAL_RADIX_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/audit/COFINAL_RADIX_REVIEW.md` |
| `signed_audit/upstream/37-wave5__signed__SIGNED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/SIGNED_PROOF.md` |
| `signed_audit/upstream/37-wave5__signed__build_signed.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/build_signed.py` |
| `signed_audit/upstream/37-wave5__signed__check_signed.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/check_signed.py` |
| `signed_audit/upstream/Coding.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Coding.lean` |
| `signed_audit/upstream/Master1.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master1.lean` |
| `signed_audit/upstream/Master2.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master2.lean` |
| `signed_audit/upstream/Master3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean` |
| `signed_audit/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `signed_audit/upstream/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `signed_audit/upstream/Packing.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Packing.lean` |
| `signed_audit/upstream/PackingBounds.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/PackingBounds.lean` |
| `signed_audit/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `signed_audit/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `signed_audit/upstream/Section4.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Section4.lean` |
| `sun/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `sun/generated/coefficient_aliases.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/generated/COEFFICIENT_ALIASES.json` |
| `sun/sources/INDEPENDENT_MATHEMATICAL_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/INDEPENDENT_MATHEMATICAL_REVIEW.md` |
| `sun/sources/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `sun/sources/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `sun/sources/SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `sun/sources/build_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/build_signed10.py` |
| `sun/sources/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `sun/sources/data/INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/INSTANCE.json` |
| `sun/sources/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `sun/sources/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `sun/sources/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `sun/sources/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `sun/sources/data/beta_sun.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta_sun.bin.gz` |
| `sun/sources/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `sun/sources/data/constants.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/constants.json` |
| `sun/sources/data/index_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/index_bound.json` |
| `sun/sources/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `sun/sources/generated/norm3_polynomial.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/generated/norm3_polynomial.json` |
| `sun/sources/verify_signed10.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/verify_signed10.py` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `native/SHA256SUMS.json` | not staged: checksum ledger |
| `positive/SHA256SUMS.json` | not staged: checksum ledger |

### `45-multioutput/` (`con-zfc-multioutput-22e75dd6b8.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `nine/upstream/COMPACT_CONSTANTS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed16/data/reference_instance/constants_upstream.json` |
| `nine/upstream/Master2.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/Master2.lean` |
| `nine/upstream/Master3.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/Master3.lean` |
| `nine/upstream/NineRatio.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineRatio.lean` |
| `nine/upstream/NineRatio_copy.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineRatio.lean` |
| `nine/upstream/NineReduce.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineReduce.lean` |
| `positive/upstream/INHERITED_POSITIVE12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/positive12/upstream/POSITIVE12_PROOF.md` |
| `positive/upstream/SHIFTED12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/positive/SHIFTED12_PROOF.md` |
| `positive/upstream/build_shifted.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/positive/build_shifted.py` |
| `requirements.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/requirements.txt` |
| `review/sources/31-sun10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `review/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `review/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `review/sources/31-sun10/quartic31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/README.md` |
| `review/sources/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `review/sources/31-sun10/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/report.tex` |
| `review/sources/31-sun10/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `review/sources/31-sun10/sections/low_degree.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/low_degree.tex` |
| `review/sources/31-sun10/sections/overview.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/overview.tex` |
| `review/sources/31-sun10/sections/parent.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/parent.tex` |
| `review/sources/31-sun10/sections/reproduction.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/reproduction.tex` |
| `review/sources/31-sun10/sections/signed16.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/signed16.tex` |
| `review/sources/31-sun10/signed10/SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `review/sources/32-integer15/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/README.md` |
| `review/sources/32-integer15/metrics.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/metrics.tex` |
| `review/sources/32-integer15/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/report.tex` |
| `review/sources/33-signed16/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/README.md` |
| `review/sources/33-signed16/coefficients_small/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/coefficients_small/section.tex` |
| `review/sources/33-signed16/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/report.tex` |
| `review/sources/34-integer14/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/README.md` |
| `review/sources/34-integer14/report/synthesis_report.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/report/synthesis_report.md` |
| `review/sources/35-cancel12/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/README.md` |
| `review/sources/35-cancel12/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/report.tex` |
| `review/sources/35-cancel12/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/coefficients.tex` |
| `review/sources/35-cancel12/sections/positive.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/positive.tex` |
| `review/sources/35-cancel12/sections/quartic.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/quartic.tex` |
| `review/sources/35-cancel12/sections/signed.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/signed.tex` |
| `review/sources/35-cancel12/sections/verification.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/verification.tex` |
| `review/sources/36-small-tuple/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/README.md` |
| `review/sources/36-small-tuple/closing_sections.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/closing_sections.tex` |
| `review/sources/36-small-tuple/nine_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/nine_section.tex` |
| `review/sources/36-small-tuple/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/report.tex` |
| `review/sources/37-wave5/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/README.md` |
| `review/sources/37-wave5/lowdegree/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/section.tex` |
| `review/sources/37-wave5/nine/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/section.tex` |
| `review/sources/37-wave5/positive/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/section.tex` |
| `review/sources/37-wave5/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/report.tex` |
| `review/sources/37-wave5/signed/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/section.tex` |
| `sun/data/parent_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `sun/upstream/signed10/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `sun/upstream/signed10/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `sun/upstream/signed10/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `sun/upstream/signed10/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `sun/upstream/signed10/data/beta_sun.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta_sun.bin.gz` |
| `audit/ISOLATED_REPLAY.log` | not staged: log file (`*.log`) |
| `short/SHORT_AUDIT_CHECK.log` | not staged: log file (`*.log`) |

## Placement record: batch 223 (wave 7)

Intake record, not a delivered file. The eight archives of the arrival
commit `4b4349064a` ("Con(ZFC) in Diophantine form (wave-7)") were extracted
straight from the committed ZIPs into numbered directories 46–53, with the
single wrapper directory removed. Nothing was edited and nothing was run at
intake.

**Waves 5 and 6 are kept.** By Vladimir's direction, wave 7 is placed beside them
(sources 31–45), not instead of them; this section is appended to the
earlier records above. The report had moved from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/` to
`Computability/DiophantineConsistency/` in `ea8ae71167`, before this pin.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 and wave-6 files of this report, which stay in the tree. The tables below
  name the shortest repository path holding the same bytes. Licence, notice
  and attribution files are always kept. All eight packages pin
  `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

To rerun a package, extract its archive from the arrival commit into a
scratch directory and run it there:

```sh
git show 4b4349064a:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `46-selective/` | `con-zfc-selective-2026-10-23.zip` | 122 | 81 | 41 | 0 | `con-zfc-selective/` |
| `47-sparse-support/` | `ConZFC_Sparse_Support_2026-10-23.zip` | 179 | 115 | 64 | 0 | `con_zfc_sparse_support_2026_10_23/` |
| `48-majorants/` | `con-zfc-support-majorants-2026-10-23.zip` | 143 | 94 | 48 | 1 | `con-zfc-support-2026-10-23/` |
| `49-support-pell/` | `con_zfc_sparse_support_2026-10-23.zip` | 177 | 134 | 42 | 1 | `con_zfc_sparse_support_2026-10-23/` |
| `50-midpoint11/` | `ConZFC_Support_Sensitive_2026-10-23.zip` | 164 | 92 | 72 | 0 | `conzfc_support_sensitive_2026-10-23/` |
| `51-sparse-arith/` | `con_zfc_sparse_arithmetic_2026-10-23.zip` | 175 | 82 | 92 | 1 | `con_zfc_sparse_arithmetic_2026-10-23/` |
| `52-sparse-pell/` | `con-zfc-sparse-pell-124c07c0b7.zip` | 331 | 237 | 94 | 0 | `con-zfc-sparse-pell-124c07c0b7/` |
| `53-selective-quad/` | `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` | 280 | 208 | 71 | 1 | `ZFC_Diophantine_Selective_Quadratic/` |

Total: 1571 members.

### `46-selective/` (`con-zfc-selective-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `certificates/coefficient_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/certificates/coefficient_bound.json` |
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `coefficient_adapter/FACTORIZED_RECEIVERS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` |
| `coefficient_adapter/build_factorized.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/research_candidate/build_factorized.py` |
| `coefficient_adapter/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficient_adapter/source44_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `nine/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/upstream/MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `nine/upstream/build_multitarget_nine.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/build_multitarget_nine.py` |
| `nine/upstream/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `short/UPSTREAM_SHORT_SYSTEM.md` | `Computability/DiophantineConsistency/SHORT_SYSTEM.md` |
| `short/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/COEFFICIENT_BINDING.json` |
| `short/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/K.bin.gz` |
| `short/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/MC.bin.gz` |
| `short/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/MF_source.bin.gz` |
| `short/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/beta.bin.gz` |
| `short/upstream_p75.json` | `Computability/DiophantineConsistency/circuits/p75_sos.json` |
| `upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/FINALIZER_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/FINALIZER_REVIEW.md` |
| `upstream/JONES_NINE_RATIO.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/PARENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/RETAINED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `upstream/ZFC.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean` |
| `upstream/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream/parent_sparse.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/parent_sparse.json` |
| `upstream/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `upstream/source40_build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/code/build.py` |
| `upstream/source40_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/report.tex` |
| `upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |

### `47-sparse-support/` (`ConZFC_Sparse_Support_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `construction/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `construction/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `construction/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `construction/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `construction/coefficients/fixed/a000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0002.bin.gz` |
| `construction/coefficients/fixed/a001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0001.bin.gz` |
| `construction/coefficients/fixed/a003.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0000.bin.gz` |
| `construction/coefficients/fixed/a004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0006.bin.gz` |
| `construction/coefficients/fixed/a005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0005.bin.gz` |
| `construction/coefficients/fixed/a006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0004.bin.gz` |
| `construction/coefficients/fixed/a007.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0003.bin.gz` |
| `construction/coefficients/fixed/a017.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0011.bin.gz` |
| `construction/coefficients/fixed/a018.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0010.bin.gz` |
| `construction/coefficients/fixed/a019.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0009.bin.gz` |
| `construction/coefficients/fixed/a020.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0008.bin.gz` |
| `construction/coefficients/fixed/a021.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0007.bin.gz` |
| `construction/coefficients/fixed/a022.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0015.bin.gz` |
| `construction/coefficients/fixed/a023.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0014.bin.gz` |
| `construction/coefficients/fixed/a024.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0013.bin.gz` |
| `construction/coefficients/fixed/a025.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0012.bin.gz` |
| `construction/coefficients/fixed/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/generated/fixed/base_floor.bin.gz` |
| `construction/coefficients/fixed10/c000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0000.bin.gz` |
| `construction/coefficients/fixed10/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0010.bin.gz` |
| `construction/coefficients/fixed10/c014.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0015.bin.gz` |
| `construction/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `construction/targets_original.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `evidence/31-sun10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `evidence/31-sun10/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `evidence/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `evidence/31-sun10/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `evidence/31-sun10/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `evidence/31-sun10/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `evidence/31-sun10/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `evidence/31-sun10/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `evidence/31-sun10/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `evidence/31-sun10/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `evidence/31-sun10/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `evidence/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `evidence/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `evidence/31-sun10/quartic31/upstream/27-wave4/operations/upstream/RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `evidence/31-sun10/quartic31/upstream/30-quartic31/arithmetic/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `evidence/31-sun10/sources/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `evidence/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` |
| `evidence/31-sun10/sources/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `evidence/31-sun10/sources/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `evidence/40-packing10/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/report.tex` |
| `evidence/45-multioutput/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/README.md` |
| `evidence/45-multioutput/nine/MULTITARGET_INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_INSTANCE.json` |
| `evidence/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `evidence/45-multioutput/nine/build_multitarget_nine.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/build_multitarget_nine.py` |
| `evidence/45-multioutput/nine/materialize_fixed_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/materialize_fixed_coefficients.py` |
| `evidence/45-multioutput/quartic/QUADRATIC_MULTI_TARGET_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_MULTI_TARGET_PROOF.md` |
| `evidence/45-multioutput/weights/MULTI_OUTPUT_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/weights/MULTI_OUTPUT_EXTRACTION_PROOF.md` |
| `evidence/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `evidence/active/SHORT_EQUATION.md` | `Computability/DiophantineConsistency/SHORT_EQUATION.md` |
| `evidence/active/SHORT_FRONTIER.md` | `Computability/DiophantineConsistency/SHORT_FRONTIER.md` |
| `evidence/active/SHORT_SYSTEM.md` | `Computability/DiophantineConsistency/SHORT_SYSTEM.md` |
| `minima/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `minima/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `minima/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `minima/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `minima/upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `minima/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `minima/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |

### `48-majorants/` (`con-zfc-support-majorants-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `code/sparse_arithmetic.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/code/audit_parent_packing.py` |
| `code/upstream40.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/code/build.py` |
| `code/upstream45.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/build_multitarget_nine.py` |
| `data/fixed/base_floor.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/data/beta_source.bin.gz` |
| `data/fixed/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `data/fixed/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `data/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `data/ports/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `data/ports/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `data/ports/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `data/ports/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `inherited/31-sun10/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `inherited/31-sun10/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `inherited/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/31-sun10/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `inherited/31-sun10/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `inherited/31-sun10/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `inherited/31-sun10/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `inherited/31-sun10/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `inherited/31-sun10/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `inherited/31-sun10/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `inherited/31-sun10/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `inherited/31-sun10/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `inherited/31-sun10/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `inherited/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `inherited/31-sun10/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `inherited/31-sun10/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `inherited/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `inherited/31-sun10/signed10/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `inherited/40-packing10/code/audit_parent_packing.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/code/audit_parent_packing.py` |
| `inherited/40-packing10/code/build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/code/build.py` |
| `inherited/40-packing10/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/report.tex` |
| `inherited/45-multioutput/nine/MULTITARGET_INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_INSTANCE.json` |
| `inherited/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `inherited/45-multioutput/nine/build_multitarget_nine.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/build_multitarget_nine.py` |
| `inherited/45-multioutput/nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `inherited/45-multioutput/quartic/QUADRATIC_TARGETS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `inherited/45-multioutput/report/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/report/report.tex` |
| `inherited/45-multioutput/weights/MULTI_OUTPUT_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/weights/MULTI_OUTPUT_EXTRACTION_PROOF.md` |
| `upstream/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean` |
| `upstream/Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/KEndpoint215.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/KEndpoint215.lean` |
| `upstream/Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `upstream/Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_ORDINARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `SHA256SUMS` | not staged: checksum ledger |

### `49-support-pell/` (`con_zfc_sparse_support_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `audits/INHERITED_ORDINARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `audits/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `audits/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `audits/INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/short/upstream/INHERITED_RETAINED59_PROOF.md` |
| `certificates/coefficient_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/certificates/coefficient_bound.json` |
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/43-sidon10/circuit.py` |
| `coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/coefficients.tex` |
| `coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/COEFFICIENT_PROOF.md` |
| `coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/coefficient_backend/k215_transitions.json` |
| `coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/wang943_tiles.json` |
| `data/coefficient_recipes.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/data/coefficient_recipes.json` |
| `fixed/positive9/a000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0002.bin.gz` |
| `fixed/positive9/a001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0001.bin.gz` |
| `fixed/positive9/a003.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0000.bin.gz` |
| `fixed/positive9/a004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0006.bin.gz` |
| `fixed/positive9/a005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0005.bin.gz` |
| `fixed/positive9/a006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0004.bin.gz` |
| `fixed/positive9/a007.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0003.bin.gz` |
| `fixed/positive9/a017.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0011.bin.gz` |
| `fixed/positive9/a018.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0010.bin.gz` |
| `fixed/positive9/a019.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0009.bin.gz` |
| `fixed/positive9/a020.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0008.bin.gz` |
| `fixed/positive9/a021.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0007.bin.gz` |
| `fixed/positive9/a022.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0015.bin.gz` |
| `fixed/positive9/a023.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0014.bin.gz` |
| `fixed/positive9/a024.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0013.bin.gz` |
| `fixed/positive9/a025.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0012.bin.gz` |
| `fixed/positive9/base_floor.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/generated/fixed/base_floor.bin.gz` |
| `fixed/signed10/c000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0000.bin.gz` |
| `fixed/signed10/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0010.bin.gz` |
| `upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/upstream/SIGNED10_PROOF.md` |
| `upstream/native/BLANK_HELICAL_PROOF_PACKAGE31.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `upstream/native/FIXED_BLANK_67_PROOF_PACKAGE31.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `upstream/native/ORDINARY_BLANK_PROOF_PACKAGE31.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `upstream/native/PELL_LEMMA_AUDIT_PACKAGE31.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/parent_sparse.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/parent_sparse.json` |
| `upstream/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/positive/upstream/quartic31_system.json` |
| `SHA256SUMS` | not staged: checksum ledger |

### `50-midpoint11/` (`ConZFC_Support_Sensitive_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/upstream/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/upstream/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `coefficients/upstream/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `coefficients/upstream/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `coefficients/upstream/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `coefficients/upstream/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/upstream/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/upstream/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/upstream/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/upstream/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `coefficients/upstream/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `coefficients/upstream/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `coefficients/upstream/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/upstream/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `packing/certificates/coefficient_bound.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/certificates/coefficient_bound.json` |
| `packing/code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `packing/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `packing/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `packing/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `packing/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `packing/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `packing/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `packing/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `packing/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `packing/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `packing/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `packing/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `packing/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `packing/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `packing/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `packing/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `packing/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `packing/data/coefficient_recipes.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/data/coefficient_recipes.json` |
| `packing/nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `packing/upstream/NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `packing/upstream/P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `packing/upstream/PARENT_TRANSPORT_SHIFT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `packing/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `packing/upstream/SUN_FINALIZER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/FINALIZER_REVIEW.md` |
| `packing/upstream/SUN_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/MULTITARGET_AUDIT.md` |
| `packing/upstream/parent_sparse.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/parent_sparse.json` |
| `packing/upstream/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `packing/upstream/parent_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `provenance/comparisons/38-batching11-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/README.md` |
| `provenance/comparisons/38-eleven-product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_product.json` |
| `provenance/comparisons/38-eleven-translated-product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_translated_product.json` |
| `provenance/comparisons/40-packing10-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/README.md` |
| `provenance/comparisons/44-b4-sparse-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/README.md` |
| `provenance/comparisons/45-multioutput-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/README.md` |
| `provenance/compiler_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `provenance/compiler_proofs/COLLECTION_AT_PIN.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/sources/README.md` |
| `provenance/compiler_proofs/DIGIT_CIRCUIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` |
| `provenance/compiler_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `provenance/compiler_proofs/NINE31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/NINE31_SOURCE_PROOF.md` |
| `provenance/compiler_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `provenance/compiler_proofs/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `provenance/compiler_proofs/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `provenance/compiler_proofs/SIGNED17_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/signed17_proof.md` |
| `provenance/endpoint/KEndpoint215.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/KEndpoint215.lean` |
| `provenance/endpoint/ZFC.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean` |
| `provenance/parents/38-ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `provenance/parents/38-OPTIONAL_TRANSLATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md` |
| `provenance/parents/44-POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `provenance/repository/SHORT_EQUATION.md` | `Computability/DiophantineConsistency/SHORT_EQUATION.md` |
| `provenance/repository/SHORT_FRONTIER.md` | `Computability/DiophantineConsistency/SHORT_FRONTIER.md` |
| `provenance/repository/SHORT_SYSTEM.md` | `Computability/DiophantineConsistency/SHORT_SYSTEM.md` |

### `51-sparse-arith/` (`con_zfc_sparse_arithmetic_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `code/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `coefficients/native31/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/native31/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `coefficients/native31/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/native31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `coefficients/native31/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `coefficients/native31/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `coefficients/native31/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `coefficients/native31/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `coefficients/native31/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/native31/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `coefficients/native31/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/native31/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `coefficients/native31/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/native31/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `coefficients/native31/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/native31/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `coefficients/native31/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `coefficients/native31/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `coefficients/native31/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/native31/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/payloads/beta_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/data/beta_source.bin.gz` |
| `coefficients/payloads/c000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `coefficients/payloads/c002.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/payloads/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `data/weights.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/data/weights.json` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/circuit.py` |
| `short/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/COEFFICIENT_BINDING.json` |
| `short/coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/INDEPENDENT_AUDIT.json` |
| `short/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `short/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/README.md` |
| `short/coefficients/SOURCES.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/SOURCES.json` |
| `short/coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/audit_coefficients.py` |
| `short/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `short/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/K.bin.gz` |
| `short/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/MC.bin.gz` |
| `short/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/MF_source.bin.gz` |
| `short/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/coefficients/beta.bin.gz` |
| `short/coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `short/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `short/coefficients/source_proofs/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `short/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `short/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `short/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `short/coefficients/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `short/coefficients/source_proofs/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `short/coefficients/source_proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `short/coefficients/source_proofs/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `short/coefficients/source_proofs/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `short/coefficients/source_proofs/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `short/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `short/upstream/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `short/upstream/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `short/upstream/p69_unscaled.json` | `Computability/DiophantineConsistency/circuits/p69_unscaled.json` |
| `short/upstream/p73_sos.json` | `Computability/DiophantineConsistency/circuits/p73_sos.json` |
| `short/upstream/p75_sos.json` | `Computability/DiophantineConsistency/circuits/p75_sos.json` |
| `short/upstream/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Common/Pell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/Pell.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Common/PellMod.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Factorial.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Factorial.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Ineq.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Ineq.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Ineq3.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Ineq3.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Lemma23.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Lemma23.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/MR.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/MR.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Theorem39.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Theorem39.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Theorem39b.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Theorem39b.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1976/Wilson.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1976/Wilson.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1978/Binomial.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1978/Binomial.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1978/Lemma210.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1978/Lemma210.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1978/Lemma28.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1978/Lemma28.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1982/Exponential.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Exponential.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1982/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1982/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1982/Psi.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Psi.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1982/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1984/Identities.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1984/Identities.lean` |
| `upstream/JONES_RATIO_LEAN/Diophantine/Paper1984/Masking.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1984/Masking.lean` |
| `upstream/JONES_RATIO_LEAN/upstream_build_metadata/lake-manifest.json` | `lake-manifest.json` |
| `upstream/JONES_RATIO_LEAN/upstream_build_metadata/lakefile.toml` | `lakefile.toml` |
| `upstream/JONES_RATIO_LEAN/upstream_build_metadata/lean-toolchain` | `lean-toolchain` |
| `upstream/PACKAGE40_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/report.tex` |
| `upstream/PACKAGE45_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `upstream/PARENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `upstream/parent_sparse.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/upstream/parent_sparse.json` |
| `upstream/parent_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `SHA256SUMS` | not staged: checksum ledger |

### `52-sparse-pell/` (`con-zfc-sparse-pell-124c07c0b7.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `inherited/nine/NineRatio.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineRatio.lean` |
| `inherited/sources/31-sun10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `inherited/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `inherited/sources/31-sun10/quartic31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/README.md` |
| `inherited/sources/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `inherited/sources/31-sun10/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/report.tex` |
| `inherited/sources/31-sun10/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `inherited/sources/31-sun10/sections/low_degree.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/low_degree.tex` |
| `inherited/sources/31-sun10/sections/overview.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/overview.tex` |
| `inherited/sources/31-sun10/sections/parent.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/parent.tex` |
| `inherited/sources/31-sun10/sections/reproduction.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/reproduction.tex` |
| `inherited/sources/31-sun10/sections/signed16.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/signed16.tex` |
| `inherited/sources/31-sun10/signed10/SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `inherited/sources/32-integer15/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/README.md` |
| `inherited/sources/32-integer15/metrics.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/metrics.tex` |
| `inherited/sources/32-integer15/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/report.tex` |
| `inherited/sources/33-signed16/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/README.md` |
| `inherited/sources/33-signed16/coefficients_small/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/coefficients_small/section.tex` |
| `inherited/sources/33-signed16/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/report.tex` |
| `inherited/sources/34-integer14/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/README.md` |
| `inherited/sources/34-integer14/report/synthesis_report.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/report/synthesis_report.md` |
| `inherited/sources/35-cancel12/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/README.md` |
| `inherited/sources/35-cancel12/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/report.tex` |
| `inherited/sources/35-cancel12/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/coefficients.tex` |
| `inherited/sources/35-cancel12/sections/positive.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/positive.tex` |
| `inherited/sources/35-cancel12/sections/quartic.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/quartic.tex` |
| `inherited/sources/35-cancel12/sections/signed.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/signed.tex` |
| `inherited/sources/35-cancel12/sections/verification.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/verification.tex` |
| `inherited/sources/36-small-tuple/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/README.md` |
| `inherited/sources/36-small-tuple/closing_sections.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/closing_sections.tex` |
| `inherited/sources/36-small-tuple/nine_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/nine_section.tex` |
| `inherited/sources/36-small-tuple/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/report.tex` |
| `inherited/sources/37-wave5/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/README.md` |
| `inherited/sources/37-wave5/lowdegree/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/section.tex` |
| `inherited/sources/37-wave5/nine/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/section.tex` |
| `inherited/sources/37-wave5/positive/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/section.tex` |
| `inherited/sources/37-wave5/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/report.tex` |
| `inherited/sources/37-wave5/signed/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/section.tex` |
| `inherited/sun/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `integer/data/parent_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `integer/fixed/K0.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `integer/fixed/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `integer/fixed/MF.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `integer/fixed/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `integer/fixed/beta_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/data/beta_source.bin.gz` |
| `integer/fixed/q003.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `integer/fixed/q008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine/data/source_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `packing/data/source_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `positive/upstream/38-batching11__eleven__ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `positive/upstream/38-batching11__eleven__OPTIONAL_TRANSLATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md` |
| `positive/upstream/44-b4-sparse__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `positive/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `report/build.sh` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/report/build.sh` |
| `requirements.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/requirements.txt` |
| `review/postpin/COMPILER_JONES.md` | `Computability/DiophantineConsistency/COMPILER_JONES.md` |
| `review/postpin/QUARTIC_COMPILER.md` | `Computability/DiophantineConsistency/QUARTIC_COMPILER.md` |
| `review/sources/31-sun10/quartic31/INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/INSTANCE.json` |
| `review/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `review/sources/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/quartic31_system60.json` |
| `review/sources/35-cancel12/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `review/sources/38-batching11/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/README.md` |
| `review/sources/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `review/sources/38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md` |
| `review/sources/38-batching11/eleven/generated/absorbed_index_eleven_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_product.json` |
| `review/sources/38-batching11/eleven/generated/absorbed_index_eleven_shifted_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_shifted_system.json` |
| `review/sources/38-batching11/eleven/generated/absorbed_index_eleven_translated_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_translated_product.json` |
| `review/sources/38-batching11/eleven/generated/absorbed_index_eleven_translated_shifted_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/generated/absorbed_index_eleven_translated_shifted_system.json` |
| `review/sources/39-direct10/DIRECT_QUADRATIC_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/DIRECT_QUADRATIC_PROOF.md` |
| `review/sources/39-direct10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/README.md` |
| `review/sources/39-direct10/optional_compact/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/COEFFICIENT_BINDING.json` |
| `review/sources/39-direct10/optional_compact/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/PROOF.md` |
| `review/sources/40-packing10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/README.md` |
| `review/sources/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` |
| `review/sources/41-bose-chowla/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/41-bose-chowla/README.md` |
| `review/sources/42-additive-b4/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/README.md` |
| `review/sources/43-sidon10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/43-sidon10/README.md` |
| `review/sources/44-b4-sparse/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/README.md` |
| `review/sources/44-b4-sparse/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `review/sources/44-b4-sparse/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `review/sources/44-b4-sparse/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `review/sources/44-b4-sparse/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `review/sources/44-b4-sparse/positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `review/sources/44-b4-sparse/positive/full_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/full_product.json` |
| `review/sources/44-b4-sparse/positive/full_shifted_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/full_shifted_system.json` |
| `review/sources/44-b4-sparse/positive/short_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/short_product.json` |
| `review/sources/44-b4-sparse/positive/short_shifted_system.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/short_shifted_system.json` |
| `review/sources/45-multioutput/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/README.md` |
| `review/sources/PLACEMENT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/PLACEMENT.md` |

### `53-selective-quad/` (`ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `batching/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `batching/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `batching/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `batching/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `batching/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `batching/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `batching/upstream/NORMALIZED_COMPILER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/positive12/upstream/POSITIVE12_PROOF.md` |
| `batching/upstream/RATIO12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/positive12/upstream/RATIO12_PROOF.md` |
| `batching/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `batching/upstream/TWELVE_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `batching/upstream/TWELVE_POSITIVE_PROOF_PINNED.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `batching/upstream/build_positive_reference.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/build_positive.py` |
| `batching/upstream/eleven/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `batching/upstream/eleven/OPTIONAL_TRANSLATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md` |
| `batching/upstream/eleven/build_eleven.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/build_eleven.py` |
| `batching/upstream/eleven/build_eleven_translated.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/build_eleven_translated.py` |
| `batching/upstream/nine/build_nine.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/nine/build_nine.py` |
| `batching/upstream/sections/section_eleven.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/sections/section_eleven.tex` |
| `batching/upstream/sections/section_nine.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/sections/section_nine.tex` |
| `build_report.sh` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/161-selectors-build.sh` |
| `jones/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `jones/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `jones/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `jones/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `jones/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `jones/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `jones/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `jones/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `jones/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `jones/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `jones/upstream/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/NEAR_SQUARE_FINALIZER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/nine/NINE_B4_PROOF.md` |
| `nine/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `nine/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine/upstream/upstream_QUADRATIC_TARGETS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `nine/upstream/upstream_parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `packing/mask_popcount/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `packing/mask_popcount/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `packing/mask_popcount/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `packing/mask_popcount/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `packing/mask_popcount/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `packing/mask_popcount/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `packing/mask_popcount/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `packing/mask_popcount/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `packing/mask_popcount/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `requirements.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/requirements.txt` |
| `short/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `short/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `short/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `short/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `short/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `short/upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/07-native-fiber-source-PELL_RELAXED_AUXILIARY_PROOF.md` |
| `short/upstream/circuits__p75_sos.json` | `Computability/DiophantineConsistency/circuits/p75_sos.json` |
| `short/upstream_verified/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `short/upstream_verified/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `short/upstream_verified/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `short/upstream_verified/SHORT_EQUATION.md` | `Computability/DiophantineConsistency/SHORT_EQUATION.md` |
| `short/upstream_verified/SHORT_SYSTEM.md` | `Computability/DiophantineConsistency/SHORT_SYSTEM.md` |
| `short/upstream_verified/tools__audit_sos_circuit.py` | `Computability/DiophantineConsistency/tools/audit_sos_circuit.py` |
| `short/upstream_verified/tools__build_short_circuit.py` | `Computability/DiophantineConsistency/tools/build_short_circuit.py` |
| `short/upstream_verified/tools__build_sos_circuit.py` | `Computability/DiophantineConsistency/tools/build_sos_circuit.py` |
| `weights/upstream_QUADRATIC_TARGETS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `weights/upstream_parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `SHA256SUMS.json` | not staged: checksum ledger |

## Placement record: batch 224 (wave 8)

Intake record, not a delivered file. The six archives of the arrival
commit `7331974b69` ("Con(ZFC) in Diophantine form (wave-8)") were extracted
straight from the committed ZIPs into numbered directories 54–59, with the
single wrapper directory removed. Nothing was edited and nothing was run at
intake.

**Waves 5–7 are kept.** By Vladimir's direction, wave 8 is placed beside them
(sources 31–53), not instead of them; this section is appended to the
earlier records above. The report had moved from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/` to
`Computability/DiophantineConsistency/` in `ea8ae71167`, before these pins.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 to wave-7 files of this report, which stay in the tree. The tables below
  name the shortest repository path holding the same bytes. Licence, notice
  and attribution files are always kept. The packages pin the wave-7
  arrival `4b4349064a` (54–57, 59) or its placement `6d375f2d2d` (58);
  59 also reviews 56 and 57, which reached it during packaging.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

To rerun a package, extract its archive from the arrival commit into a
scratch directory and run it there:

```sh
git show 7331974b69:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `54-calibrated-carry/` | `con-zfc-calibrated-carry-4b4349064a.zip` | 383 | 288 | 95 | 0 | `con-zfc-calibrated-carry-4b4349064a/` |
| `55-congruence-norms/` | `con_zfc_congruence_norms_2026-10-23.zip` | 393 | 99 | 294 | 0 | `con_zfc_congruence_norms_2026-10-23/` |
| `56-free-coordinate/` | `ConZFC_Free_Coordinate_2026-10-23.zip` | 120 | 73 | 45 | 2 | `con_zfc_free_coordinate_2026-10-23/` |
| `57-separated-degrees/` | `ConZFC_Separated_Degrees_2026-10-23.zip` | 191 | 95 | 96 | 0 | `con-zfc-separated-degrees-2026-10-23/` |
| `58-integral-root/` | `ConZFC_Integral_Root_2026-10-23.zip` | 111 | 61 | 50 | 0 | `ConZFC_Integral_Root_2026-10-23/` |
| `59-degree-separated/` | `ZFC_Diophantine_Degree_Separated_2026-10-23.zip` | 538 | 358 | 179 | 1 | `ZFC_Diophantine_Degree_Separated/` |

Total: 1736 members.

### `54-calibrated-carry/` (`con-zfc-calibrated-carry-4b4349064a.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `inherited/ADDITIONAL_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/inherited/ADDITIONAL_SOURCE_PINS.json` |
| `inherited/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/inherited/SOURCE_PINS.json` |
| `inherited/arrivals/ZFC_Diophantine_Selective_Quadratic_2026-10-23/nine/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `inherited/arrivals/ZFC_Diophantine_Selective_Quadratic_2026-10-23/weights/SELECTIVE_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/SELECTIVE_EXTRACTION_PROOF.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/coefficient_adapter/FACTORIZED_RECEIVERS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/coefficient_adapter/source44_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/upstream/P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/upstream/PARENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `inherited/arrivals/con-zfc-selective-2026-10-23/upstream/RETAINED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `inherited/arrivals/con-zfc-support-majorants-2026-10-23/inherited/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `inherited/arrivals/con-zfc-support-majorants-2026-10-23/proofs/HIGHER_MAJORANT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/HIGHER_MAJORANT.md` |
| `inherited/arrivals/con-zfc-support-majorants-2026-10-23/proofs/NINE_T2048_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/NINE_T2048_REVIEW.md` |
| `inherited/arrivals/con-zfc-support-majorants-2026-10-23/proofs/NINE_WEIGHT_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/NINE_WEIGHT_REVIEW.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/FINALIZER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/FINALIZER_PROOF.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/short/coefficients/source_proofs/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `inherited/direct/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `inherited/direct/sources/39-direct10/DIRECT_QUADRATIC_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/DIRECT_QUADRATIC_PROOF.md` |
| `inherited/direct/sources/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/research_candidate/FACTORIZED_RECEIVERS.md` |
| `inherited/direct/sources/44-b4-sparse/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `inherited/nine/NineRatio.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineRatio.lean` |
| `inherited/sources/31-sun10/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/README.md` |
| `inherited/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `inherited/sources/31-sun10/quartic31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/README.md` |
| `inherited/sources/31-sun10/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `inherited/sources/31-sun10/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/report.tex` |
| `inherited/sources/31-sun10/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `inherited/sources/31-sun10/sections/low_degree.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/low_degree.tex` |
| `inherited/sources/31-sun10/sections/overview.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/overview.tex` |
| `inherited/sources/31-sun10/sections/parent.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/parent.tex` |
| `inherited/sources/31-sun10/sections/reproduction.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/reproduction.tex` |
| `inherited/sources/31-sun10/sections/signed16.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/signed16.tex` |
| `inherited/sources/31-sun10/signed10/SIGNED10_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_SECTION.tex` |
| `inherited/sources/32-integer15/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/README.md` |
| `inherited/sources/32-integer15/metrics.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/metrics.tex` |
| `inherited/sources/32-integer15/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/report.tex` |
| `inherited/sources/33-signed16/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/README.md` |
| `inherited/sources/33-signed16/coefficients_small/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/coefficients_small/section.tex` |
| `inherited/sources/33-signed16/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/report.tex` |
| `inherited/sources/34-integer14/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/README.md` |
| `inherited/sources/34-integer14/report/synthesis_report.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/report/synthesis_report.md` |
| `inherited/sources/35-cancel12/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/README.md` |
| `inherited/sources/35-cancel12/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/report.tex` |
| `inherited/sources/35-cancel12/sections/coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/coefficients.tex` |
| `inherited/sources/35-cancel12/sections/positive.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/positive.tex` |
| `inherited/sources/35-cancel12/sections/quartic.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/quartic.tex` |
| `inherited/sources/35-cancel12/sections/signed.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/signed.tex` |
| `inherited/sources/35-cancel12/sections/verification.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sections/verification.tex` |
| `inherited/sources/36-small-tuple/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/README.md` |
| `inherited/sources/36-small-tuple/closing_sections.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/closing_sections.tex` |
| `inherited/sources/36-small-tuple/nine_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/nine_section.tex` |
| `inherited/sources/36-small-tuple/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/report.tex` |
| `inherited/sources/37-wave5/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/README.md` |
| `inherited/sources/37-wave5/lowdegree/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/section.tex` |
| `inherited/sources/37-wave5/nine/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/nine/section.tex` |
| `inherited/sources/37-wave5/positive/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/positive/section.tex` |
| `inherited/sources/37-wave5/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/report.tex` |
| `inherited/sources/37-wave5/signed/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/signed/section.tex` |
| `inherited/sun/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `integer/data/parent_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `integer/fixed/K0.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/K.bin.gz` |
| `integer/fixed/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MC.bin.gz` |
| `integer/fixed/MF.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MF_source.bin.gz` |
| `integer/fixed/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/beta.bin.gz` |
| `integer/fixed/q407e689ef089.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/beta.bin.gz` |
| `integer/fixed/qf44e64e75f39.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/beta.bin.gz` |
| `native/INHERITED_SEPARATED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/SEPARATED_PROOF.md` |
| `native/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/K.bin.gz` |
| `native/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MC.bin.gz` |
| `native/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MF_source.bin.gz` |
| `native/UPSTREAM_SOURCES.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/SOURCES.json` |
| `native/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/beta.bin.gz` |
| `native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine/fixed/4164b9c631e09c57f30d0699bd9146c106fed18a2829e5220033d2c06b3001b7.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MC.bin.gz` |
| `nine/fixed/456b39f7b82cc935374b729b223221fbf34864e43b699fe94504caad06969d0f.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/beta.bin.gz` |
| `nine/fixed/4e094dca3a2cfb839d73f94bfd90ccf9168804d7204f35176b01646885885336.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/MF_source.bin.gz` |
| `nine/fixed/c41628eebbbc8bdfb4ca0246969963713eeffc337039a98cbe075b1727e24aa8.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/coefficient_adapter/separated_coefficients/K.bin.gz` |
| `packing/data/source_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `positive/upstream/INHERITED_P66.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/generated/p66_degree157.json` |
| `positive/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive/upstream/SELECTIVE_NORM_MINIMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/short/RESULT.md` |
| `positive/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `requirements.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/requirements.txt` |
| `source/data/source_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |

### `55-congruence-norms/` (`con_zfc_congruence_norms_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `fourteen/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `fourteen/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `fourteen/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `fourteen/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `fourteen/upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `fourteen/upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `fourteen/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `fourteen/upstream/FOURTEEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `fourteen/upstream/MINIMA_PROOF.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/MINIMA_PROOF.txt` |
| `fourteen/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `fourteen/upstream/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `fourteen/upstream/fourteen_positive_degree56.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/fourteen_positive.json` |
| `native/calibration/DOMINATED_CALCULUS_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `native/calibration/PARTIAL_SELECTOR_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/proof.md` |
| `native/calibration/PERMUTED_SOURCE_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/proof.md` |
| `native/calibration/README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `native/calibration/UPSTREAM_FORMAL_STATUS.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `native/calibration/UPSTREAM_LEAN_REPRODUCTION.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/README.md` |
| `native/calibration/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `native/calibration/proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `native/calibration/source_calibration.tex` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/gc-zc215/proofs/inherited_calibration.tex` |
| `native/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `native/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `native/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `native/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `native/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `native/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `native/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `native/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `native/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `native/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `native/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `native/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `native/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Containers.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Containers.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254GIC.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254GIC.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CodeOrder.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CodeOrder.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CompositionModel.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/CompositionModel.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Constructible.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Constructible.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleAbs.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleAbs.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleDef.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleDef.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleOrder.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleOrder.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleReflect.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleReflect.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleZF.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag219.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag219.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag219Bisim.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag219Bisim.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DagDom.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DagDom.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DagPerm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DagPerm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DeepPositiveClosure.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DeepPositiveClosure.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FiniteSetsCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FiniteSetsCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FramedWindow.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FramedWindow.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InductiveAttemptsCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InductiveAttemptsCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalOrd.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalOrd.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalRank.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalRank.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalWO.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/InternalWO.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk000.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk000.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk001.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk001.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk002.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk002.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk003.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk003.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk004.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk004.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk005.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk005.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk006.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk006.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk007.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk007.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk008.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk008.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk009.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk009.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk010.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk010.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk011.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk011.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk012.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215Chunk012.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDenseBridge.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDenseBridge.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEqCodes222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEqCodes222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KFast215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KFast215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KFastSites215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KFastSites215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KHome.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KHome.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KHomeReady.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KHomeReady.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerEqv.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerEqv.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRaw.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRaw.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRel.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRel.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerTag.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerTag.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Basic.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Basic.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Collect.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Collect.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Model.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Model.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Power.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Power.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ReplacementNative.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ReplacementNative.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Separation.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Separation.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQHyp.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQHyp.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KRuntimeCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KRuntimeCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeed222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeed222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSim.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSim.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch000.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch000.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch001.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch001.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch002.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch002.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch003.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch003.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch004.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch004.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch005.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch005.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch006.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch006.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch007.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch007.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch008.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215Batch008.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck00.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck00.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck01.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck01.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck02.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck02.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck03.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck03.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck04.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck04.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck05.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck05.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck06.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck06.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck07.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck07.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck08.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck08.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck09.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck09.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck10.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck10.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck11.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck11.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck12.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck12.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck13.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck13.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck14.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck14.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck15.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215FwdCheck15.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Program.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Program.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable230.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable230.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTableCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTableCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTape.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTape.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZip.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZip.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZipTape.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZipTape.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Kalmar.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Kalmar.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Control222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Control222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Lib222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Lib222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Macros222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Macros222.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Perm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Perm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2RootPerm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2RootPerm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedForm254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedForm254.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedZF.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/OrderRec.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/OrderRec.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PositiveClosure.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PositiveClosure.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PowerSets.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PowerSets.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PowerSyntax.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PowerSyntax.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileAxioms.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileAxioms.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCollection.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCollection.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileComposition.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileComposition.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCongruence.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCongruence.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileModel.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileModel.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfilePairs.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfilePairs.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileSyntax.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileSyntax.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDag.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDag.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDagIteration.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDagIteration.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMEquiv.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMEquiv.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMNormalizedBisim.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMNormalizedBisim.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMTransfer.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMTransfer.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPathClean.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPathClean.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SatSupport.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SatSupport.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedPerm.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedPerm.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SingletonInfinityCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SingletonInfinityCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SiteCoverage.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SiteCoverage.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiCalculus.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiCalculus.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiClean.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiClean.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiComplete.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiComplete.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiDerived.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiDerived.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiFalsity.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiFalsity.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiLeibniz.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiLeibniz.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TransRec.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TransRec.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TupleOrder.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TupleOrder.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModelCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModelCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFRelativization.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFRelativization.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPartCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPartCore.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` |
| `native/k215_formal/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFRank.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFRank.lean` |
| `native/k215_formal/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/EndpointAudit215.lean` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/EndpointAudit215.lean` |
| `native/k215_formal/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/K215Audit.lean` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/K215Audit.lean` |
| `native/k215_formal/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py` |
| `native/k215_formal/Logic/FirstOrder/Lean/FirstOrder/Calculus.lean` | `Logic/FirstOrder/Lean/FirstOrder/Calculus.lean` |
| `native/k215_formal/Logic/FirstOrder/Lean/FirstOrder/Completeness.lean` | `Logic/FirstOrder/Lean/FirstOrder/Completeness.lean` |
| `native/k215_formal/Logic/FirstOrder/Lean/FirstOrder/Fol.lean` | `Logic/FirstOrder/Lean/FirstOrder/Fol.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Basic.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Basic.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodePredicate.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodePredicate.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/FormulaClosedSet.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/FormulaClosedSet.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSat.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSat.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSatTotality.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSatTotality.lean` |
| `native/k215_formal/SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/OmegaRecursion.lean` | `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/OmegaRecursion.lean` |
| `native/k215_formal/SetTheory/ZF/Lean/ZF/Zf.lean` | `SetTheory/ZF/Lean/ZF/Zf.lean` |
| `native/k215_formal/lean-toolchain` | `lean-toolchain` |
| `native/proofs/nine_ratio/MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` |
| `native/proofs/nine_ratio/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `native/proofs/nine_ratio/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `native/proofs/nine_ratio/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `native/proofs/ordinary_native/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `native/proofs/ordinary_native/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` |
| `native/proofs/ordinary_native/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `native/proofs/ordinary_native/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `native/proofs/ordinary_native/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` |
| `native/proofs/ordinary_native/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `native/proofs/ordinary_native/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `native/proofs/ordinary_native/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `native/proofs/ordinary_native/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `native/proofs/ordinary_native/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `native/proofs/ordinary_native/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `native/proofs/ordinary_native/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `native/proofs/ordinary_native/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `native/proofs/ordinary_native/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `native/proofs/ordinary_native/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `native/proofs/ordinary_native/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `native/proofs/ordinary_native/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `native/proofs/ordinary_native/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `native/proofs/ordinary_native/fixed_factor_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `native/proofs/ordinary_native/mixed125_full_interface.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `native/proofs/ordinary_native/pell_fixed_affine_exponent52.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` |
| `native/proofs/ordinary_native/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `native/proofs/ordinary_native/wang943_language.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `native/proofs/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine_fast/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/COEFFICIENT_BINDING.json` |
| `nine_fast/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/SOURCE_PINS.json` |
| `nine_fast/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `nine_fast/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine_fast/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine_fast/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine_fast/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine_fast/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine_fast/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_fast/upstream/NEAR_SQUARE_FINALIZER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/nine/NINE_B4_PROOF.md` |
| `nine_fast/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine_fast/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine_fast/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `nine_fast/upstream/SELECTIVE_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/upstream/SELECTIVE_EXTRACTION_PROOF.md` |
| `nine_fast/upstream/SELECTIVE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/SOURCE_PINS.json` |
| `nine_fast/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine_fast/upstream/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/SOURCE_PINS.json` |
| `nine_fast/upstream/code_v1.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `nine_fast/upstream/nine__MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/upstream/MULTITARGET_NINE_PROOF_PACKAGE45.md` |
| `nine_fast/upstream/source_support.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/source_support.json` |
| `nine_fast/upstream/upstream_QUADRATIC_TARGETS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `nine_fast/upstream/upstream_parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine_fast/upstream/verify_selective.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/verify_selective.py` |
| `nine_majorant/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/COEFFICIENT_BINDING.json` |
| `nine_majorant/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/SOURCE_PINS.json` |
| `nine_majorant/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `nine_majorant/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine_majorant/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine_majorant/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine_majorant/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine_majorant/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine_majorant/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_majorant/upstream/HIGHER_MAJORANT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/HIGHER_MAJORANT.md` |
| `nine_majorant/upstream/NEAR_SQUARE_FINALIZER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/nine/NINE_B4_PROOF.md` |
| `nine_majorant/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine_majorant/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine_majorant/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `nine_majorant/upstream/SELECTIVE_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/upstream/SELECTIVE_EXTRACTION_PROOF.md` |
| `nine_majorant/upstream/SELECTIVE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/SOURCE_PINS.json` |
| `nine_majorant/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine_majorant/upstream/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/SOURCE_PINS.json` |
| `nine_majorant/upstream/code_v1.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `nine_majorant/upstream/nine__MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/upstream/MULTITARGET_NINE_PROOF_PACKAGE45.md` |
| `nine_majorant/upstream/source_support.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/source_support.json` |
| `nine_majorant/upstream/upstream_QUADRATIC_TARGETS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/quartic/QUADRATIC_TARGETS.json` |
| `nine_majorant/upstream/upstream_parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine_majorant/upstream/verify_selective.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/weights/verify_selective.py` |
| `ten/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/SOURCE_PINS.json` |
| `ten/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/circuit.py` |
| `ten/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `ten/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `ten/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `ten/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `ten/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `ten/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `ten/evaluate.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/evaluate.py` |
| `ten/parameters_shifted_legacy.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `ten/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `ten/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `ten/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |

### `56-free-coordinate/` (`ConZFC_Free_Coordinate_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `nine/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/COEFFICIENT_BINDING.json` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `nine/upstream/SELECTIVE_EXTRACTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/upstream/SELECTIVE_EXTRACTION_PROOF.md` |
| `nine/upstream/SELECTIVE_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `nine/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine/upstream/SPARSE_PELL_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `nine/upstream/code_v1.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `nine/upstream/source60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `nine/upstream/upstream_parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `short/coefficients31/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `short/coefficients31/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `short/coefficients31/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `short/coefficients31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `short/coefficients31/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `short/coefficients31/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `short/coefficients31/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `short/coefficients31/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `short/coefficients31/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `short/coefficients31/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `short/coefficients31/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `short/coefficients31/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `short/coefficients31/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `short/coefficients31/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `short/coefficients31/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `short/coefficients31/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `short/coefficients31/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `short/coefficients31/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `short/coefficients31/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `short/coefficients31/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `short/upstream/GAP_AUXILIARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/short/historical/GAP_AUXILIARY_PROOF.md` |
| `short/upstream/GAP_MINIMA.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/minima_supplement.tex` |
| `short/upstream/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `short/upstream/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `short/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `short/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `short/upstream/gap_minima75.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/gap_minima75.json` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `nine/SHA256SUMS.json` | not staged: checksum ledger |

### `57-separated-degrees/` (`ConZFC_Separated_Degrees_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/COEFFICIENT_BINDING.json` |
| `coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/INDEPENDENT_AUDIT.json` |
| `coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/PROOF.md` |
| `coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/README.md` |
| `coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/audit_coefficients.py` |
| `coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/build_coefficients.py` |
| `coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/upstream/36-small-tuple/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `coefficients/upstream/36-small-tuple/source_proofs/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `coefficients/upstream/36-small-tuple/source_proofs/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `fixed/coefficient_05.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q004.bin.gz` |
| `fixed/coefficient_07.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `fixed/coefficient_08.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `fixed/coefficient_09.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q000.bin.gz` |
| `fixed/coefficient_10.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q007.bin.gz` |
| `low_degree/upstream/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `low_degree/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `low_degree/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `quartic/quartic50_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json` |
| `quartic/upstream/33-signed16/upstream/fixed_blank67_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `quartic/upstream/34-integer14/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `quartic/upstream/34-integer14/coefficients/BUILD_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic/upstream/34-integer14/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `quartic/upstream/34-integer14/coefficients/INDEPENDENT_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/INDEPENDENT_CHECKS.json` |
| `quartic/upstream/34-integer14/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `quartic/upstream/34-integer14/coefficients/REPLAY_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/REPLAY_CHECKS.json` |
| `quartic/upstream/34-integer14/coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `quartic/upstream/34-integer14/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `quartic/upstream/34-integer14/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `quartic/upstream/34-integer14/coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic/upstream/34-integer14/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `quartic/upstream/34-integer14/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `quartic/upstream/34-integer14/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `quartic/upstream/34-integer14/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `quartic/upstream/34-integer14/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `quartic/upstream/34-integer14/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `quartic/upstream/34-integer14/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `quartic/upstream/34-integer14/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `quartic/upstream/34-integer14/coefficients/sources/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `quartic/upstream/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `quartic/upstream/34-integer14/coefficients/sources/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `quartic/upstream/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` |
| `quartic/upstream/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `quartic/upstream/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `quartic/upstream/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `quartic/upstream/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` |
| `quartic/upstream/34-integer14/coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `quartic/upstream/34-integer14/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `quartic/upstream/34-integer14/coefficients/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `quartic/upstream/34-integer14/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `quartic/upstream/34-integer14/low_degree/QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `quartic/upstream/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `quartic/upstream/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `quartic/upstream/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `upstream/logical_calibration/CHOICE_CALIBRATION.md` | `Computability/BusyBeaver/Research/ZFC/choice_calibration254.md` |
| `upstream/logical_calibration/K215_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/logical_calibration/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `upstream/logical_calibration/SOURCE_CALIBRATION.tex` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/gc-zc215/proofs/inherited_calibration.tex` |
| `upstream/native_parent/31-sun10/quartic31/upstream/27-wave4/operations/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/27-wave4/operations/PROOF.md` |
| `upstream/native_parent/31-sun10/quartic31/upstream/27-wave4/operations/upstream/RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `upstream/native_parent/31-sun10/quartic31/upstream/30-quartic31/arithmetic/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/COLLECTION_AT_PIN.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/sources/README.md` |
| `upstream/native_parent/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/DIGIT_CIRCUIT_SOURCE_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/NINE31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/NINE31_SOURCE_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/native_parent/31-sun10/sources/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream/native_parent/31-sun10/sources/SIGNED17_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/signed17_proof.md` |
| `upstream/nine__MULTITARGET_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/upstream/MULTITARGET_NINE_PROOF_PACKAGE45.md` |
| `upstream/wave7_calibrated_nine_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/build_nine.py` |
| `upstream/wave7_calibrated_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `upstream/wave7_margin_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `upstream/wave7_sun_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/build.py` |
| `upstream/wave7_sun_popcount.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/section.tex` |

### `58-integral-root/` (`ConZFC_Integral_Root_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/native_report.pdf` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.pdf` |
| `coefficients/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `coefficients/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `coefficients/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `coefficients/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `coefficients/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `coefficients/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `coefficients/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `coefficients/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `coefficients/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `coefficients/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `coefficients/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `coefficients/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `coefficients/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `coefficients/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `twelve/upstream/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `twelve/upstream/INNER_RECOVERY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/positive/PROOF.md` |
| `twelve/upstream/LEAN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `twelve/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `twelve/upstream/build_absorbed.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/build_absorbed.py` |
| `twelve/upstream/check_absorbed.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/check_absorbed.py` |
| `twelve/upstream/positive12_none_lean_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/positive12_none_lean_product.json` |
| `upstream/ARITHMETIC_PRIOR_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/README.md` |
| `upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `upstream/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `upstream/MINIMA44_PRIOR.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/gap_minima75.json` |
| `upstream/MINIMA44_PRIOR.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/minima_supplement.tex` |
| `upstream/MINIMA44_PRIOR_PROOF.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/minima/MINIMA_PROOF.txt` |
| `upstream/OFFSET44_PRIOR.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/sections/short.tex` |
| `upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/P67_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/RELAXED_KERNEL_COMPLETE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/short/PROOF.md` |
| `upstream/SELECTIVE_PRIOR_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/README.md` |
| `upstream/SPARSE_PELL_PRIOR_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/README.md` |
| `upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |

### `59-degree-separated/` (`ZFC_Diophantine_Degree_Separated_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `encoding/parent_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine/coefficients/old_tuple/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/old_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/old_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/old_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/coefficients/old_tuple/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine/coefficients/packet52_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json` |
| `nine/data/CERTIFICATE_174_interior_packed.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_packed.json` |
| `nine/data/CERTIFICATE_174_interior_regular.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_regular.json` |
| `nine/data/CERTIFICATE_174_interior_shifted.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_shifted.json` |
| `nine/data/parent_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine/data/source_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `nine/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine/upstream/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `nine/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine/upstream/compiler_coefficient_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/native_tuple_matching_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/PROOF.md` |
| `nine/upstream/native_tuple_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `nine/upstream/old_tuple_complete_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/packet52_conditional_separation.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/audit/CONDITIONAL_SEPARATION_THEOREM.md` |
| `nine/upstream/packet52_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `nine/upstream/packet53_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `nine_free_adjunct/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/circuit.py` |
| `nine_free_adjunct/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `nine_free_adjunct/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `nine_free_adjunct/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `nine_free_adjunct/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine_free_adjunct/coefficients/old_tuple/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine_free_adjunct/coefficients/old_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine_free_adjunct/coefficients/old_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine_free_adjunct/coefficients/old_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine_free_adjunct/coefficients/old_tuple/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine_free_adjunct/coefficients/packet52_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json` |
| `nine_free_adjunct/data/CERTIFICATE_174_interior_packed.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_packed.json` |
| `nine_free_adjunct/data/CERTIFICATE_174_interior_regular.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_regular.json` |
| `nine_free_adjunct/data/CERTIFICATE_174_interior_shifted.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_shifted.json` |
| `nine_free_adjunct/data/parent_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `nine_free_adjunct/data/source_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `nine_free_adjunct/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine_free_adjunct/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine_free_adjunct/upstream/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `nine_free_adjunct/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine_free_adjunct/upstream/compiler_coefficient_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_free_adjunct/upstream/native_tuple_matching_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/PROOF.md` |
| `nine_free_adjunct/upstream/native_tuple_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `nine_free_adjunct/upstream/old_tuple_complete_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_free_adjunct/upstream/packet52_conditional_separation.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/audit/CONDITIONAL_SEPARATION_THEOREM.md` |
| `nine_free_adjunct/upstream/packet52_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `nine_free_adjunct/upstream/packet53_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `positive/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/batching/COEFFICIENT_BINDING.json` |
| `positive/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `positive/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `positive/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `positive/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `positive/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `positive/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `positive/upstream/FOURTEEN_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `positive/upstream/LEAN_TWELVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `positive/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `positive13_adjunct/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/COEFFICIENT_BINDING.json` |
| `positive13_adjunct/coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/INDEPENDENT_AUDIT.json` |
| `positive13_adjunct/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/PROOF.md` |
| `positive13_adjunct/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/README.md` |
| `positive13_adjunct/coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/audit_coefficients.py` |
| `positive13_adjunct/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/coefficients/build_coefficients.py` |
| `positive13_adjunct/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive13_adjunct/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive13_adjunct/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive13_adjunct/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive13_adjunct/coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/COEFFICIENT_TRANSFER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/COEFFICIENT_TRANSFER.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/package24_prime_padding.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/package25_mixed_clauses.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `positive13_adjunct/coefficients/upstream/36-small-tuple/source_proofs/package27_complete_transfer.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `positive13_adjunct/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive13_adjunct/requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `positive13_adjunct/upstream/low_degree/upstream/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `positive13_adjunct/upstream/low_degree/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive13_adjunct/upstream/low_degree/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `requirements.txt` | `SetTheory/Cardinals/docs/reports/quaternionic-analysis/slice-regularity-and-fueter-inversion/data/08-reflection-residue-energy-requirements.txt` |
| `review/LATE_CATALOGUE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/README.md` |
| `review/LATE_PROPOSAL_REVIEW.md` | `Computability/DiophantineConsistency/PROPOSAL_REVIEW.md` |
| `review/LATE_REPLAY_free_coordinate_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/LATE_REPLAY_free_coordinate_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/LATE_REPLAY_separated_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/LATE_REPLAY_separated_optimized.stdout.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/input_1_ConZFC_Sparse_Support_2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/47-sparse-support/README.md` |
| `review/input_2_ConZFC_Support_Sensitive_2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/README.md` |
| `review/input_3_ZFC_Diophantine_Selective_Quadratic_2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/README.md` |
| `review/input_4_con-zfc-selective-2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/46-selective/README.md` |
| `review/input_5_con-zfc-sparse-pell-124c07c0b7.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/README.md` |
| `review/input_6_con-zfc-support-majorants-2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/README.md` |
| `review/input_7_con_zfc_sparse_arithmetic_2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/README.md` |
| `review/input_8_con_zfc_sparse_support_2026-10-23.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/README.md` |
| `root_checks/ABSOLUTE_PATH_SCAN.json` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake212-catalogue/diagnostics.json` |
| `root_checks/encoding__test_split__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/encoding__test_split__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/encoding__verify_split__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/encoding__verify_split__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/nine__independent_review__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/nine__independent_review__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/nine__verify_nine__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/nine__verify_nine__optimized.stdout.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/positive__build_ordinary_merger__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/positive__check_merger_independent__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/positive__check_merger_independent__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/positive__check_ordinary_merger__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/positive__check_ordinary_merger__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/short__audit__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/short__audit__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/short__build__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/signed__check_jones__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/signed__check_jones__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/signed__check_source_minimum_independent__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/signed__check_source_minimum_independent__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/sun__independent_check__optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `root_checks/sun__reproduce__normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `short/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `short/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `short/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `short/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `short/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `short/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `short/upstream/FOURTEEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `short/upstream/GAP_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/short/PROOF.md` |
| `short/upstream/INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `short/upstream/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `short/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `short/upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `short/upstream/RELAXED_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/short/PROOF.md` |
| `short/upstream/SHORT_EQUATION.md` | `Computability/DiophantineConsistency/SHORT_EQUATION.md` |
| `short/upstream/SHORT_SYSTEM.md` | `Computability/DiophantineConsistency/SHORT_SYSTEM.md` |
| `short/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `signed/CODE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `signed/FIXED_BINDING_OLD_SOURCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/FIXED_BINDING.json` |
| `signed/RATIO_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/RATIO_SOURCE_PINS.json` |
| `signed/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/SOURCE_PINS.json` |
| `signed/b4_support.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/b4_support.py` |
| `signed/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/circuit.py` |
| `signed/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `signed/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `signed/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `signed/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `signed/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `signed/generated/signed_degree.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/generated/signed_degree.json` |
| `signed/generated/signed_seeded_degree.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/generated/signed_seeded_degree.json` |
| `signed/split/parent_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `signed/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `signed/upstream/CRT_SPARSE_PELL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `signed/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `signed/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `signed/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `signed/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed/upstream/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `sun/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/SOURCE_PINS.json` |
| `sun/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `sun/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `sun/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `sun/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `sun/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `sun/data/parent_quartic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/quartic31.json` |
| `sun/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `sun/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `sun/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `SHA256SUMS.json` | not staged: checksum ledger |
