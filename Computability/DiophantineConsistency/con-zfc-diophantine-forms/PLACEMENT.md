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
