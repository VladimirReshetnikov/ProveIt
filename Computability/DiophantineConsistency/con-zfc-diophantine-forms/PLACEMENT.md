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

## Placement record: batch 225 (wave 9)

Intake record, not a delivered file. The eight archives of the arrival
commit `0c6be9a074` ("Con(ZFC) in Diophantine form (wave-9)") were extracted
straight from the committed ZIPs into numbered directories 60–67, with the
single wrapper directory removed. Nothing was edited and nothing was run at
intake.

**Waves 5–8 are kept.** By Vladimir's direction, wave 9 is placed beside them
(sources 31–59), not instead of them; this section is appended to the
earlier records above. The report had moved from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/` to
`Computability/DiophantineConsistency/` in `ea8ae71167`, before these pins.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 to wave-8 files of this report, which stay in the tree. The tables below
  name the shortest repository path holding the same bytes. Licence, notice
  and attribution files are always kept. All eight packages pin the wave-8
  placement `beb0192cb8`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

To rerun a package, extract its archive from the arrival commit into a
scratch directory and run it there:

```sh
git show 0c6be9a074:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `60-positive-gap/` | `ConZFC_Positive_Gap_2026-10-23.zip` | 206 | 94 | 104 | 8 | `positive-gap-refinement/` |
| `61-congruence-carriers/` | `con-zfc-congruence-carriers.zip` | 125 | 73 | 51 | 1 | `con-zfc-congruence-carriers/` |
| `62-sign-and-norm/` | `con-zfc-sign-and-norm.zip` | 234 | 123 | 93 | 18 | `con-zfc-sign-and-norm/` |
| `63-sign-recovery/` | `con-zfc-sign-recovery-2026-10-23.zip` | 125 | 67 | 58 | 0 | `con-zfc-sign-recovery/` |
| `64-structural-reductions/` | `con-zfc-structural-reductions-2026-10-23.zip` | 161 | 85 | 75 | 1 | `con-zfc-structural-reductions/` |
| `65-shared-taps/` | `con_zfc_shared_taps_carriers_2026-10-23.zip` | 179 | 102 | 77 | 0 | `con_zfc_shared_taps_carriers/` |
| `66-gap-congruence/` | `ConZFC_Gap_Congruence_2026-10-23.zip` | 296 | 190 | 102 | 4 | `con-zfc-gap-congruence/` |
| `67-oriented-guards/` | `ZFC_Diophantine_Oriented_Guards_2026-10-23.zip` | 503 | 296 | 206 | 1 | `ZFC_Diophantine_Oriented_Guards/` |

Total: 1829 members.

### `60-positive-gap/` (`ConZFC_Positive_Gap_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `checks/replay_01.log` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `checks/replay_02.log` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `checks/replay_03.log` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `research_low_degree/supplement15/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `research_low_degree/supplement15/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `research_low_degree/supplement15/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `research_low_degree/supplement15/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `research_low_degree/supplement15/native/REBUILT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `research_low_degree/supplement15/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `research_low_degree/supplement15/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `research_low_degree/supplement15/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `research_low_degree/supplement15/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `research_low_degree/supplement15/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `research_low_degree/supplement15/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `research_low_degree/supplement15/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `research_low_degree/supplement15/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `research_low_degree/supplement15/native/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `research_low_degree/supplement15/native/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `research_low_degree/supplement15/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `research_low_degree/supplement15/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `research_low_degree/supplement15/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `research_low_degree/supplement15/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `research_low_degree/supplement15/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `research_low_degree/supplement15/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `research_low_degree/supplement15/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `research_low_degree/supplement15/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `research_low_degree/supplement15/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `research_low_degree/supplement15/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `research_low_degree/supplement15/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `research_low_degree/supplement15/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `research_low_degree/supplement15/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `research_low_degree/supplement15/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `research_low_degree/supplement15/upstream/OBJECT_ZFC.md` | `Computability/DiophantineConsistency/OBJECT_ZFC.md` |
| `research_low_degree/supplement15/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `research_low_degree/supplement15/upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `research_nine/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `research_nine/compact_candidate/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `research_nine/compact_candidate/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `research_nine/compact_candidate/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `research_nine/compact_candidate/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `research_nine/compact_candidate/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `research_nine/upstream/free_coordinate_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/nine/PROOF.md` |
| `research_nine/upstream/free_coordinate_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/review/free_C_review.md` |
| `research_nine/upstream/frozen_nine_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/PROOF.md` |
| `upstream-status/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream-status/OBJECT_ZFC.md` | `Computability/DiophantineConsistency/OBJECT_ZFC.md` |
| `upstream31/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `upstream31/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `upstream31/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream31/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `upstream31/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `upstream31/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `upstream31/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `upstream31/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `upstream31/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `upstream31/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `upstream31/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `upstream31/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `upstream31/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `upstream31/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `upstream31/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `upstream31/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `upstream31/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `upstream31/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `upstream31/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream31/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream31/quartic31/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `upstream31/quartic31/parent_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `upstream31/quartic31/quartic31_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `upstream31/signed10/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/circuit.py` |
| `upstream31/sources/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `upstream31/sources/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream31/sources/NINE31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/NINE31_SOURCE_PROOF.md` |
| `upstream31/sources/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream31/sources/QUARTIC31_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `upstream44/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `upstream44/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `upstream44/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `upstream44/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `upstream44/native/REBUILT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `upstream44/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `upstream44/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `upstream44/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `upstream44/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `upstream44/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `upstream44/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `upstream44/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `upstream44/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream44/native/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `upstream44/native/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `upstream44/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `upstream44/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `upstream44/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `upstream44/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `upstream44/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `upstream44/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `upstream44/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream44/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `upstream44/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `upstream44/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream44/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream44/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream44/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream44/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `checks/replay_04.log` | not staged: log file (`*.log`) |
| `checks/replay_05.log` | not staged: log file (`*.log`) |
| `checks/replay_06.log` | not staged: log file (`*.log`) |
| `checks/replay_07.log` | not staged: log file (`*.log`) |
| `checks/replay_08.log` | not staged: log file (`*.log`) |
| `checks/replay_09.log` | not staged: log file (`*.log`) |
| `checks/replay_10.log` | not staged: log file (`*.log`) |
| `checks/replay_11.log` | not staged: log file (`*.log`) |

### `61-congruence-carriers/` (`con-zfc-congruence-carriers.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/compact44/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `coefficients/compact44/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `coefficients/compact44/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `coefficients/compact44/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `coefficients/compact44/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `coefficients/compact44/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `coefficients/compact44/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `coefficients/compact44/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `integer/coefficients_source/BUILD_REPLAY.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/coefficients_source/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `integer/coefficients_source/INDEPENDENT_REPLAY.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/INDEPENDENT_CHECKS.json` |
| `integer/coefficients_source/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/coefficients_source/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `integer/coefficients_source/coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `integer/coefficients_source/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/coefficients_source/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/coefficients_source/coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/coefficients_source/coefficients/sources/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `integer/coefficients_source/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `integer/coefficients_source/coefficients/sources/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `integer/coefficients_source/coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer/coefficients_source/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/coefficients_source/coefficients/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `integer/coefficients_source/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/coefficients_source/generated_payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/coefficients_source/generated_payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `integer/coefficients_source/generated_payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer/coefficients_source/generated_payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `integer/coefficients_source/generated_payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer/coefficients_source/generated_payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `integer/coefficients_source/generated_payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer/coefficients_source/generated_payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `integer/coefficients_source/generated_payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/coefficients_source/historical/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer/coefficients_source/low_degree/QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `integer/coefficients_source/low_degree/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/SOURCE_LEDGER.json` |
| `integer/coefficients_source/low_degree/quartic50.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json` |
| `integer/coefficients_source/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `integer/upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `integer/upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `provenance/INHERITED_ORDINARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `provenance/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `provenance/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `provenance/signed_source/ELEVEN_POSITIVE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md` |
| `provenance/signed_source/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `provenance/source57_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/README.md` |
| `provenance/source57_low_degree_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/low_degree/PROOF.md` |
| `provenance/source58_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/README.md` |
| `provenance/source58_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `provenance/source59_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/README.md` |
| `provenance/source59_positive13_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/positive13_adjunct/PROOF.md` |
| `SHA256SUMS` | not staged: checksum ledger |

### `62-sign-and-norm/` (`con-zfc-sign-and-norm.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine/data/parent_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `nine/fixed/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/39-direct10/optional_compact/data/beta_source.bin.gz` |
| `nine/fixed/c001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/fixed/coefficient_00.bin.gz` |
| `nine/fixed/c004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q004.bin.gz` |
| `nine/fixed/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/fixed/coefficient_00.bin.gz` |
| `nine/fixed/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/fixed/coefficient_03.bin.gz` |
| `nine/fixed/c008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/fixed/coefficient_04.bin.gz` |
| `nine/fixed/c011.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine/fixed/c015.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q000.bin.gz` |
| `nine/fixed/c016.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/integer/fixed/q007.bin.gz` |
| `nine/upstream/COMPACT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json` |
| `nine/upstream/NATIVE_MATCHING_PROOF.md` | `Computability/DiophantineConsistency/candidates/split116-compact/compact57/provenance/interface_proof.md` |
| `nine/upstream/NATIVE_TUPLE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `nine/upstream/build_native_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `nine/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine/upstream/old_parent.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `positive13/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive13/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive13/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive13/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive13/upstream/COMPACT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json` |
| `positive13/upstream/DEGREE126_COMPARATOR.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/positive13_adjunct/PROOF.md` |
| `positive13/upstream/FOURTEEN_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `positive13/upstream/NATIVE_MATCHING_PROOF.md` | `Computability/DiophantineConsistency/candidates/split116-compact/compact57/provenance/interface_proof.md` |
| `positive13/upstream/NATIVE_TUPLE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive13/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `positive13/upstream/ORDINARY_FOURTEEN_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/review/ORDINARY_FOURTEEN_AUDIT.md` |
| `positive13/upstream/ORDINARY_MERGER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/positive/PROOF.md` |
| `positive13/upstream/build_native_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive13/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `quartic42/dependencies/12-gap-norm14/proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `quartic42/dependencies/14-integer29/dependencies/blank_helical_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/BLANK_HELICAL_PROOF.md` |
| `quartic42/dependencies/14-integer29/dependencies/fixed_blank_67_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `quartic42/dependencies/14-integer29/proofs/signed_domain_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `quartic42/dependencies/K215/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `quartic42/dependencies/K215/proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `quartic42/dependencies/Pell/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `quartic42/dependencies/Pell/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `quartic42/dependencies/Pell/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `quartic42/dependencies/Pell/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `quartic42/dependencies/Pell/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `quartic42/dependencies/Pell/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `quartic42/dependencies/Pell/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `quartic42/dependencies/Pell/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `quartic42/dependencies/native/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `quartic42/dependencies/source34/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `quartic42/dependencies/source34/PORTABILITY_TRANSFORMS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/PORTABILITY_TRANSFORMS.json` |
| `quartic42/dependencies/source34/audit/COEFFICIENT_SEMANTIC_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/audit/COEFFICIENT_SEMANTIC_REVIEW.md` |
| `quartic42/dependencies/source34/audit/COFINAL_RADIX_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/audit/COFINAL_RADIX_REVIEW.md` |
| `quartic42/dependencies/source34/coefficients/BUILD_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic42/dependencies/source34/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `quartic42/dependencies/source34/coefficients/INDEPENDENT_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/INDEPENDENT_CHECKS.json` |
| `quartic42/dependencies/source34/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `quartic42/dependencies/source34/coefficients/REPLAY_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/REPLAY_CHECKS.json` |
| `quartic42/dependencies/source34/coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `quartic42/dependencies/source34/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `quartic42/dependencies/source34/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `quartic42/dependencies/source34/coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic42/dependencies/source34/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `quartic42/dependencies/source34/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `quartic42/dependencies/source34/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `quartic42/dependencies/source34/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `quartic42/dependencies/source34/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `quartic42/dependencies/source34/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `quartic42/dependencies/source34/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `quartic42/dependencies/source34/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `quartic42/dependencies/source34/coefficients/sources/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `quartic42/dependencies/source34/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `quartic42/dependencies/source34/coefficients/sources/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `quartic42/dependencies/source34/coefficients/sources/25-hybrid12_build_coefficients.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` |
| `quartic42/dependencies/source34/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `quartic42/dependencies/source34/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `quartic42/dependencies/source34/coefficients/sources/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `quartic42/dependencies/source34/coefficients/sources/27-wave4_build_mixed.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` |
| `quartic42/dependencies/source34/coefficients/sources/PRIME_PADDING.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `quartic42/dependencies/source34/coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `quartic42/dependencies/source34/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `quartic42/dependencies/source34/coefficients/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `quartic42/dependencies/source34/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `quartic42/dependencies/source34/low_degree/CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/CHECKS.json` |
| `quartic42/dependencies/source34/low_degree/QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `quartic42/dependencies/source34/low_degree/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/SOURCE_LEDGER.json` |
| `quartic42/dependencies/source34/low_degree/build_quartic50.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/build_quartic50.py` |
| `quartic42/dependencies/source34/low_degree/quartic50.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json` |
| `quartic42/dependencies/source34/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `quartic42/dependencies/source34/low_degree/upstream/integer51_degree4_odd_scale.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/integer51_degree4_odd_scale.json` |
| `quartic42/upstream/INHERITED_ORDINARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `quartic42/upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `quartic42/upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `verification/logs_normal/companions_independent_algebra.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/nine_complete_reconstruction.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/positive13_builder.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/positive13_formula_checker.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/positive13_independent_degree.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/quartic_builder.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/quartic_coefficients_and_dependencies.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/quartic_independent_algebra.log` | not staged: log file (`*.log`) |
| `verification/logs_normal/sextic_and_octic_restoration.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/companions_independent_algebra.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/nine_complete_reconstruction.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/positive13_builder.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/positive13_formula_checker.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/positive13_independent_degree.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/quartic_builder.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/quartic_coefficients_and_dependencies.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/quartic_independent_algebra.log` | not staged: log file (`*.log`) |
| `verification/logs_optimized/sextic_and_octic_restoration.log` | not staged: log file (`*.log`) |

### `63-sign-recovery/` (`con-zfc-sign-recovery-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/BUILD_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/INDEPENDENT_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/INDEPENDENT_CHECKS.json` |
| `coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `coefficients/REPLAY_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/REPLAY_CHECKS.json` |
| `coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/sources/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `coefficients/sources/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `coefficients/sources/25-hybrid12_build_coefficients.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` |
| `coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `coefficients/sources/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `coefficients/sources/27-wave4_build_mixed.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` |
| `coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `coefficients/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/circuit.py` |
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/data/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `nine/data/split_code.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `nine/data/split_kernels.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_kernels.json` |
| `nine/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/FREE_COORDINATE_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/upstream/HIGHER_MAJORANT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/HIGHER_MAJORANT.md` |
| `nine/upstream/SPLIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/upstream/SPLIT_SOURCE_PROOF.md` |
| `nine/upstream/free_coordinate_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/nine/PROOF.md` |
| `nine/upstream/free_coordinate_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/review/free_C_review.md` |
| `nine/upstream/frozen_nine_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/PROOF.md` |
| `upstream/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `upstream/HALF_BINOMIAL_KERNEL.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `upstream/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/LOW_DEGREE_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/lowdegree/PROOF.md` |
| `upstream/OBJECT_ZFC_STATUS.md` | `Computability/DiophantineConsistency/OBJECT_ZFC.md` |
| `upstream/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `upstream/ODD_SCALE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `upstream/QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `upstream/SIGNED_DOMAIN.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `upstream/quartic50.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json` |

### `64-structural-reductions/` (`con-zfc-structural-reductions-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer41/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer41/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer41/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer41/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer41/upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `integer41/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer41/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer41/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer41/upstream/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer41/upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `integer41/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer41/upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `integer41/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine-positive-111/coefficients/BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine-positive-111/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine-positive-111/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine-positive-111/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine-positive-111/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine-positive-111/data/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `nine-positive-111/fixed/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/base_floor.bin.gz` |
| `nine-positive-111/fixed/c002.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine-positive-111/fixed/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `nine-positive-111/fixed/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `nine-positive-111/fixed/c009.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine-positive-111/fixed/c011.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine-positive-111/fixed/c014.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `nine-positive-111/fixed/c016.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c010.bin.gz` |
| `nine-positive-111/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `nine-positive-111/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine-positive-111/native/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine-positive-111/native/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine-positive-111/native/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine-positive-111/native/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine-positive-111/native/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine-positive-111/native/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine-positive-111/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine-positive-111/upstream/FREE_NINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine-positive-111/upstream/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `nine-positive-111/upstream/SPLIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/provenance/59-source-proof.md` |
| `positive14/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive14/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `positive14/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive14/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `positive14/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive14/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive14/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive14/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive14/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive14/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive14/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive14/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive14/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `positive14/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `positive14/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive14/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive14/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive14/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive14/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive14/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive14/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive14/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive14/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive14/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive14/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive14/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positive14/native/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive14/upstream/FOURTEEN_GAP_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/fourteen/PROOF.md` |
| `positive14/upstream/FOURTEEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `positive14/upstream/INTEGRAL_ROOT_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `positive14/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `positive14/upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive14/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `positive14/upstream/TRANSPORT_SHIFT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/positive/upstream/TRANSPORT_SHIFT_PROOF.original29.md` |
| `review/package58_README.pinned.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/README.md` |
| `review/package59_README.pinned.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/README.md` |
| `certificates/LATEX_BUILD.log` | not staged: log file (`*.log`) |

### `65-shared-taps/` (`con_zfc_shared_taps_carriers_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `baseline/51-sparse-arith.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/README.md` |
| `baseline/54-calibrated-carry.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/README.md` |
| `baseline/55-congruence-norms.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/README.md` |
| `baseline/57-separated-degrees.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/README.md` |
| `baseline/58-integral-root.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/README.md` |
| `baseline/59-degree-separated.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/README.md` |
| `nine/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/coefficients/COEFFICIENT_BINDING.json` |
| `nine/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/coefficients/SOURCE_PINS.json` |
| `nine/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/coefficients/build_coefficients.py` |
| `nine/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/coefficients.tex` |
| `nine/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/coefficients/upstream/25-COEFFICIENT_PROOF.md` |
| `nine/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/COEFFICIENT_PROOF.md` |
| `nine/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine/data/source_system65.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `nine/fixed/shared_taps/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/base_floor.bin.gz` |
| `nine/fixed/shared_taps/c001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/shared_taps/c004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `nine/fixed/shared_taps/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/shared_taps/c008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `nine/fixed/shared_taps/c011.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/fixed/shared_taps/c015.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `nine/fixed/shared_taps/c016.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c010.bin.gz` |
| `nine/fixed/shared_taps_economy/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/base_floor.bin.gz` |
| `nine/fixed/shared_taps_economy/c001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/shared_taps_economy/c004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `nine/fixed/shared_taps_economy/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/shared_taps_economy/c008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `nine/fixed/shared_taps_economy/c011.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/fixed/shared_taps_economy/c015.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `nine/fixed/shared_taps_economy/c016.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c010.bin.gz` |
| `pell/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `pell/coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `pell/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `pell/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `pell/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `pell/coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `pell/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `pell/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `pell/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `pell/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `pell/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `pell/coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `pell/coefficients/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `pell/coefficients/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `pell/coefficients/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `pell/coefficients/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `pell/coefficients/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `pell/coefficients/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `pell/coefficients/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `pell/coefficients/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `pell/coefficients/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `pell/coefficients/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `pell/coefficients/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `pell/coefficients/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `pell/coefficients/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `pell/coefficients/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `pell/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `pell/upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `pell/upstream/package58_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `pell/upstream/package59_absorber.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/positive/section.tex` |
| `sun/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/circuit.py` |
| `sun/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/49-support-pell/coefficients/COEFFICIENT_BINDING.json` |
| `sun/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/42-additive-b4/sources/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `sun/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `sun/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `sun/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `sun/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `sun/data/source_system65.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/positive/upstream/quartic31_system.json` |
| `sun/inherited/package59_INSTANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/INSTANCE.json` |
| `sun/inherited/package59_build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/build.py` |
| `sun/inherited/package59_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |

### `66-gap-congruence/` (`ConZFC_Gap_Congruence_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `algebra/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `algebra/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `algebra/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `algebra/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `algebra/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `algebra/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `algebra/upstream/INTEGRAL_ROOT_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `algebra/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `algebra/upstream/PROVENANCE.source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/PROVENANCE.json` |
| `algebra/upstream/circuits/p15_degree24.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/circuits/p15_degree24.json` |
| `algebra/upstream/circuits/p15_degree26.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/circuits/p15_degree26.json` |
| `algebra/upstream/circuits/p15_degree30.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/circuits/p15_degree30.json` |
| `direct/sources/BoundedForallRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/BoundedForallRepresentation.lean` |
| `direct/sources/Bridge.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Bridge.lean` |
| `direct/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/sources/ComposeRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ComposeRepresentation.lean` |
| `direct/sources/ComputationRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ComputationRepresentation.lean` |
| `direct/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/sources/NativeFormulaGraphs.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFormulaGraphs.lean` |
| `direct/sources/NativeGraphEnumerator.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeGraphEnumerator.lean` |
| `direct/sources/QuarticCompiler.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/QuarticCompiler.lean` |
| `direct/sources/RemainderRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/RemainderRepresentation.lean` |
| `direct/sources/Representation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Representation.lean` |
| `integer/alternative_low_cost/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `integer/alternative_low_cost/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `integer/alternative_low_cost/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `integer/alternative_low_cost/data/baseline_layout.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `integer/alternative_low_cost/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/alternative_low_cost/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `integer/alternative_low_cost/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `integer/alternative_low_cost/fixed/c000.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/alternative_low_cost/fixed/c001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `integer/alternative_low_cost/fixed/c002.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `integer/alternative_low_cost/fixed/c007.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `integer/alternative_low_cost/fixed/c008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `integer/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `integer/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `integer/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `integer/data/baseline_layout.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `integer/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `integer/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `integer/fixed/c001.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/fixed/c002.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c010.bin.gz` |
| `integer/fixed/c003.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `integer/fixed/c004.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `integer/fixed/c005.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `integer/fixed/c006.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `integer/fixed/c009.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `integer/fixed/c010.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/CONGRUENCE_FINALIZER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `integer/upstream/DEGREE_SEPARATED_SOURCE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `integer/upstream/INHERITED_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/packing/mask_popcount/SOURCE_PINS.json` |
| `integer/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `integer/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/data/defect.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/nine/REFINED_DEFECT_POLYNOMIAL.json` |
| `nine/fixed/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/base_floor.bin.gz` |
| `nine/fixed/c_002b14d7312678e8.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `nine/fixed/c_08a87fa0a134af7e.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c010.bin.gz` |
| `nine/fixed/c_1f49e78f6521d0fe.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/c_3bdf564b2c00dfd7.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/fixed/c_64e7d593e0425265.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0212.magnitude.bin.gz` |
| `nine/fixed/c_a749e84ec6806d92.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/data/fixed/c002.bin.gz` |
| `nine/fixed/c_bd70eebd66b6d548.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/coefficients/payloads/c005.bin.gz` |
| `nine/fixed/c_d048f06bd476e521.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/fixed/c_e24dea94f889b837.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/fixed_leaf_payloads/c0096.magnitude.bin.gz` |
| `nine/upstream/FREE_CARRIER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine/upstream/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `nine/upstream/REFINED_MAJORANT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/nine/REFINED_MAJORANT_PROOF.md` |
| `nine/upstream/SPLIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/upstream/SPLIT_SOURCE_PROOF.md` |
| `nine/upstream/free_coordinate_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/nine/PROOF.md` |
| `nine/upstream/free_coordinate_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/review/free_C_review.md` |
| `nine/upstream/frozen_nine_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/PROOF.md` |
| `nine/upstream/old_tuple_complete_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_audit/INHERITED_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/coefficients/old_tuple/COEFFICIENT_BINDING.json` |
| `report/build.sh` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/report/build.sh` |
| `review/formal/MARGIN_FINALIZER.md` | `Computability/DiophantineConsistency/MARGIN_FINALIZER.md` |
| `review/formal/OBJECT_ZFC.md` | `Computability/DiophantineConsistency/OBJECT_ZFC.md` |
| `review/sources/ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23/data/channel_certificate108.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/data/channel_certificate.json` |
| `review/sources/ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23/data/degree_channels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/data/degree_channels.json` |
| `review/sources/ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/encoding/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/encoding/split_code.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/encoding/split_kernels.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_kernels.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/coefficients/old_tuple/COEFFICIENT_BINDING.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/coefficients/old_tuple/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/generated/split_116_positive.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/generated/split_116_positive.json` |
| `review/sources/ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated/nine_free_adjunct/generated/split_116_positive_certificate.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/generated/split_116_positive_certificate.json` |
| `source/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `source/split_code.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `algebra/SHA256SUMS.json` | not staged: checksum ledger |
| `integer_audit/SHA256SUMS.json` | not staged: checksum ledger |
| `nine/SHA256SUMS.json` | not staged: checksum ledger |

### `67-oriented-guards/` (`ZFC_Diophantine_Oriented_Guards_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `build_report.sh` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/build_report.sh` |
| `encoding/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `encoding/upstream/separated_degrees_certificate108.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/data/channel_certificate.json` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/circuit.py` |
| `nine/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/coefficients/COEFFICIENT_BINDING.json` |
| `nine/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `nine/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `nine/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `nine/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `nine/coefficients/old_tuple/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/coefficients/old_tuple/COEFFICIENT_BINDING.json` |
| `nine/coefficients/old_tuple/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine/coefficients/old_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine/coefficients/old_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine/coefficients/old_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine/coefficients/old_tuple/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `nine/coefficients/packet52_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json` |
| `nine/data/CERTIFICATE_174_interior_packed.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_packed.json` |
| `nine/data/CERTIFICATE_174_interior_regular.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_regular.json` |
| `nine/data/CERTIFICATE_174_interior_shifted.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_shifted.json` |
| `nine/data/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `nine/data/source_system60.json` | `Computability/DiophantineConsistency/data/native-quadratic52/source_system60.json` |
| `nine/data/split_code.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `nine/data/split_kernels.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_kernels.json` |
| `nine/upstream/FREE_C_BASELINE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/upstream/FREE_C_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/SOURCE_PINS.json` |
| `nine/upstream/HIGHER_MAJORANT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/48-majorants/proofs/HIGHER_MAJORANT.md` |
| `nine/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `nine/upstream/ProductPell.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean` |
| `nine/upstream/QUARTIC60_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/QUARTIC60_PROOF.md` |
| `nine/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `nine/upstream/SPLIT_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/upstream/SPLIT_SOURCE_PROOF.md` |
| `nine/upstream/compiler_coefficient_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/congruence_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/nine_majorant/PROOF.md` |
| `nine/upstream/congruence_build_nine.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/nine_majorant/build_nine.py` |
| `nine/upstream/free_coordinate_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/nine/PROOF.md` |
| `nine/upstream/free_coordinate_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/README.md` |
| `nine/upstream/free_coordinate_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/review/free_C_review.md` |
| `nine/upstream/free_coordinate_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/56-free-coordinate/provenance/SOURCE_PINS.json` |
| `nine/upstream/frozen_nine_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine/PROOF.md` |
| `nine/upstream/native_tuple_matching_proof.md` | `Computability/DiophantineConsistency/candidates/split116-compact/compact57/provenance/interface_proof.md` |
| `nine/upstream/native_tuple_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `nine/upstream/old_tuple_complete_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/upstream/packet52_conditional_separation.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/audit/CONDITIONAL_SEPARATION_THEOREM.md` |
| `nine/upstream/packet52_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `nine/upstream/packet53_nine_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/nine/PROOF.md` |
| `positive/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/coefficients/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `positive/coefficients/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `positive/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/coefficients/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/coefficients/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive/coefficients/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive/coefficients/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive/coefficients/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive/coefficients/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/coefficients/native_report.pdf` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.pdf` |
| `positive/coefficients/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `positive/coefficients/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `positive/coefficients/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `positive/coefficients/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `positive/coefficients/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/coefficients/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/coefficients/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive/coefficients/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive/coefficients/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/coefficients/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/coefficients/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive/coefficients/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/coefficients/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/coefficients/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive/coefficients/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/coefficients/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positive/upstream/FOURTEEN_ABSORBER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `positive/upstream/INTEGRAL_ROOT_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `positive/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `positive/upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `quartic/upstream/q45/AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/AUDIT.json` |
| `quartic/upstream/q45/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `quartic/upstream/q45/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/README.md` |
| `quartic/upstream/q45/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/SOURCE_PINS.json` |
| `quartic/upstream/q45/WAVE7_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/proofs/WAVE7_AUDIT.md` |
| `quartic/upstream/q45/build_verify.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/build_verify.py` |
| `quartic/upstream/q45/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `quartic/upstream/q45/quartic45_expanded.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45_expanded.json` |
| `quartic/upstream/q45/quartic50_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/quartic50.json` |
| `quartic/upstream/q45/upstream/33-signed16/upstream/fixed_blank67_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `quartic/upstream/q45/upstream/34-integer14/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/BUILD_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/INDEPENDENT_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/INDEPENDENT_CHECKS.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/REPLAY_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/REPLAY_CHECKS.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_build_coefficients.py.inert` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_build_mixed.py.inert` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `quartic/upstream/q45/upstream/34-integer14/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `quartic/upstream/q45/upstream/34-integer14/low_degree/QUARTIC50_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/QUARTIC50_PROOF.md` |
| `quartic/upstream/q45/upstream/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| `quartic/upstream/q45/upstream/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `quartic/upstream/q45/upstream/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `review/baseline/ConZFC_Free_Coordinate_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/ConZFC_Free_Coordinate_2026-10-23.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/review/LATE_REPLAY_free_coordinate_normal.stdout.txt` |
| `review/baseline/ConZFC_Integral_Root_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/ConZFC_Separated_Degrees_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/ConZFC_Separated_Degrees_2026-10-23.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/review/LATE_REPLAY_separated_normal.stdout.txt` |
| `review/baseline/ZFC_Diophantine_Degree_Separated_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con-zfc-calibrated-carry-4b4349064a.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con_zfc_congruence_norms_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed10/final_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed10/final_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed10/normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed10/optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed108/normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed108/optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed108trim/normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed108trim/optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed13/normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/signed13/optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `signed/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/circuit.py` |
| `signed/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `signed/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `signed/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `signed/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `signed/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `signed/data/layout.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/split_code.json` |
| `signed/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `signed/evaluate.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/evaluate.py` |
| `signed/generated/source_records.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/generated/source_records.json` |
| `signed/reproduce.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/reproduce.py` |
| `signed/source_audit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/source_audit.py` |
| `signed/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `signed/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `signed/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `signed/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `signed/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed108/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/circuit.py` |
| `signed108/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `signed108/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `signed108/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `signed108/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `signed108/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `signed108/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `signed108/evaluate.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/evaluate.py` |
| `signed108/reproduce.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/reproduce.py` |
| `signed108/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `signed108/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `signed108/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `signed108/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `signed108/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed108trim/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/circuit.py` |
| `signed108trim/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `signed108trim/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `signed108trim/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `signed108trim/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `signed108trim/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `signed108trim/data/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `signed108trim/reproduce.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/reproduce.py` |
| `signed108trim/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `signed108trim/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `signed108trim/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `signed108trim/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `signed108trim/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed13/CODE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/CODE.json` |
| `signed13/RATIO_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/RATIO_SOURCE_PINS.json` |
| `signed13/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/SOURCE_PINS.json` |
| `signed13/b4_support.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/b4_support.py` |
| `signed13/check_jones.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/signed/check_jones.py` |
| `signed13/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/53-selective-quad/jones/circuit.py` |
| `signed13/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `signed13/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `signed13/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `signed13/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `signed13/coefficients/original_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `signed13/split/parent_source.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `signed13/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `signed13/upstream/CRT_SPARSE_PELL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/nine/PROOF.md` |
| `signed13/upstream/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `signed13/upstream/PREVIOUS_SIGNED13_SECTION.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/signed/section.tex` |
| `signed13/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `signed13/upstream/Ratio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean` |
| `signed13/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `signed13/upstream/parent_quartic31.json` | `Computability/DiophantineConsistency/candidates/split116-compact/compact54/data/parent_source.json` |
| `SHA256SUMS.json` | not staged: checksum ledger |

## Placement record: batch 226 (wave 10)

Intake record, not a delivered file. The eight archives of the arrival
commit `9513bd88ce` ("Con(ZFC) in Diophantine form (wave-10)") were extracted
straight from the committed ZIPs into numbered directories 68–75, with the
single wrapper directory removed. Nothing was edited and nothing was run at
intake.

**Waves 5–9 are kept.** By Vladimir's direction, wave 10 is placed beside them
(sources 31–67), not instead of them; this section is appended to the
earlier records above. The report had moved from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/` to
`Computability/DiophantineConsistency/` in `ea8ae71167`, before these pins.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 to wave-9 files of this report, which stay in the tree. The tables below
  name the shortest repository path holding the same bytes. Licence, notice
  and attribution files are always kept. 75 bundles the eight wave-9 ZIPs; they are
  mapped to their arrival commit `0c6be9a074`. The packages pin the
  wave-9 placement `a2cd79b912` or the later merge `9cca523d9f`; 68, 74
  and 75 cite both.
- **Checksum ledgers, logs and TeX build artifacts.** `SHA256SUMS*`, `*.log`
  and TeX auxiliaries (`*.aux`, `*.toc`, …) are excluded by the root
  `.gitignore`; they were not verified.

To rerun a package, extract its archive from the arrival commit into a
scratch directory and run it there:

```sh
git show 9513bd88ce:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `68-joint-positivity/` | `ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.zip` | 234 | 154 | 74 | 6 | `con-zfc-joint-positivity-commutative/` |
| `69-cones-pell/` | `con-zfc-cones-pell-2026-10-23.zip` | 107 | 55 | 52 | 0 | `con-zfc-cones-pell/` |
| `70-residue-orientation/` | `con-zfc-residue-orientation-root-transfer-2026-10-23.zip` | 148 | 97 | 51 | 0 | `con-zfc-residue-orientation-root-transfer-2026-10-23/` |
| `71-determinant-guards/` | `con_zfc_calibrated_determinant_guards_2026-10-23.zip` | 144 | 87 | 57 | 0 | `con_zfc_calibrated_cones/` |
| `72-congruence-sextic/` | `con_zfc_congruence_and_sextic_2026-10-23.zip` | 117 | 73 | 44 | 0 | `con_zfc_congruence_and_sextic/` |
| `73-guard-reanchoring/` | `con_zfc_guard_reanchoring.zip` | 192 | 83 | 79 | 30 | `guard-reanchoring-and-adaptive-carriers/` |
| `74-centered-pell-gaps/` | `con-zfc-centered-pell-gaps-2026-10-23.zip` | 55 | 37 | 18 | 0 | `con-zfc-centered-pell-gaps/` |
| `75-signed-bootstrap/` | `ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip` | 195 | 117 | 65 | 13 | `ZFC_Diophantine_Signed_Bootstrap/` |

Total: 1192 members.

### `68-joint-positivity/` (`ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct_audit/inherited/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/SOURCE_PINS.json` |
| `direct_audit/inherited/sources/BoundedForallRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/BoundedForallRepresentation.lean` |
| `direct_audit/inherited/sources/Bridge.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Bridge.lean` |
| `direct_audit/inherited/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct_audit/inherited/sources/ComposeRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ComposeRepresentation.lean` |
| `direct_audit/inherited/sources/ComputationRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ComputationRepresentation.lean` |
| `direct_audit/inherited/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct_audit/inherited/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct_audit/inherited/sources/NativeFormulaGraphs.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFormulaGraphs.lean` |
| `direct_audit/inherited/sources/NativeGraphEnumerator.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeGraphEnumerator.lean` |
| `direct_audit/inherited/sources/QuarticCompiler.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/QuarticCompiler.lean` |
| `direct_audit/inherited/sources/RemainderRepresentation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/RemainderRepresentation.lean` |
| `direct_audit/inherited/sources/Representation.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Representation.lean` |
| `integer_system/inherited/SOURCE_COMPANIONS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `integer_system/inherited/octic30.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `integer_system_audit/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer_system_audit/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer_system_audit/coefficients/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `integer_system_audit/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer_system_audit/coefficients/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `integer_system_audit/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer_system_audit/coefficients/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `integer_system_audit/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer_system_audit/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/README.md` |
| `integer_system_audit/coefficients/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `integer_system_audit/coefficients/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `integer_system_audit/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer_system_audit/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer_system_audit/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer_system_audit/source/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `integer_system_audit/source/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `integer_system_audit/source/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `integer_system_audit/source/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `integer_system_audit/source/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `integer_system_audit/source/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `integer_system_audit/source/COMPANIONS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `integer_system_audit/source/PRIME_PADDING.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `integer_system_audit/source/Q42_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/PROOF.md` |
| `integer_system_audit/source/SOURCE34_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `integer_system_audit/source/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer_system_audit/source/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer_system_audit/source/octic30.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `integer_system_audit/source/quartic42_x_square.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/quartic42_x_square.json` |
| `norm/final10/data/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `norm/final10/data/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `norm/final10/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `norm/final10/data/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `norm/final10/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `norm/final10/data/source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/source/gapN86_source.json` |
| `norm/final10/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0005.bin.gz` |
| `norm/final10/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0006.bin.gz` |
| `norm/final10/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0002.bin.gz` |
| `norm/final10/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/q0011.bin.gz` |
| `norm/final10/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/sun/data/fixed/beta_sun.bin.gz` |
| `norm/final10/provenance/BASELINE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/signed/SOURCE_PINS.json` |
| `norm/final10/provenance/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `norm/final10/provenance/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `norm/final10/provenance/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `norm/final10/provenance/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `norm/final10/provenance/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `packing/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `packing/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `packing/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `packing/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `packing/coefficients/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `packing/gap87_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/source/gap87_source.json` |
| `packing/gapL86_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/source/gapL86_source.json` |
| `packing/gapN86_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/source/gapN86_source.json` |
| `packing/gapNq85_source.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/source.json` |
| `report/build.sh` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/report/build.sh` |
| `review/formal/DIRECT_PROGRAM.md` | `Computability/DiophantineConsistency/DIRECT_PROGRAM.md` |
| `review/formal/NATIVE_PELL_STEP_DOWN.md` | `Computability/DiophantineConsistency/NATIVE_PELL_STEP_DOWN.md` |
| `review/formal/SPLIT116_FORMALIZATION.md` | `Computability/DiophantineConsistency/SPLIT116_FORMALIZATION.md` |
| `review/formal/SPLIT_SOURCE_EXISTENCE.md` | `Computability/DiophantineConsistency/SPLIT_SOURCE_EXISTENCE.md` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `packing/gap87.log` | not staged: log file (`*.log`) |
| `packing/gapL86.log` | not staged: log file (`*.log`) |
| `packing/gapN86.log` | not staged: log file (`*.log`) |
| `packing/gapNq85.log` | not staged: log file (`*.log`) |
| `packing/split89.log` | not staged: log file (`*.log`) |

### `69-cones-pell/` (`con-zfc-cones-pell-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/upstream/Q41_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/Q44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/upstream/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/upstream/coefficients/sources/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer/upstream/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/upstream/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/upstream/integers/SIGNED_FAMILY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/integers/SIGNED_FAMILY_PROOF.md` |
| `integer/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positive/upstream/source61/positive/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/ACTIVE_BINDING.json` |
| `positive/upstream/source61/positive/PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive/upstream/source61/positive/PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `positive/upstream/source61/positive/build13.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/build13.py` |
| `positive/upstream/source61/positive/check13.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/check13.py` |
| `positive/upstream/source61/positive/dag.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/dag.py` |
| `positive/upstream/source61/positive/p12_product_split2.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/p12_product_split2.json` |
| `positive/upstream/source61/positive/p13_degree34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/p13_degree34.json` |
| `positive/upstream/source61/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex` |
| `review/upstream/61-congruence-carriers__README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/README.md` |
| `review/upstream/62-sign-and-norm__README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/README.md` |
| `review/upstream/64-structural-reductions__README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/README.md` |
| `review/upstream/DIRECT_GRAPH.md` | `Computability/DiophantineConsistency/DIRECT_GRAPH.md` |
| `review/upstream/EXPLICIT_EQUATION.md` | `Computability/DiophantineConsistency/EXPLICIT_EQUATION.md` |

### `70-residue-orientation/` (`con-zfc-residue-orientation-root-transfer-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `baseline/52_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/README.md` |
| `baseline/52_positive11_Y_lean_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/positive11_Y_lean_product.json` |
| `baseline/61_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/README.md` |
| `baseline/62_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/README.md` |
| `baseline/64_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/README.md` |
| `baseline/65_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/README.md` |
| `baseline/66_metrics.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/report/metrics.tex` |
| `baseline/67_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/README.md` |
| `eleven/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `eleven/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `eleven/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `eleven/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `eleven/upstream/compact44_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `eleven/upstream/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `eleven/upstream/compact44_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `eleven/upstream/package52_Y_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `eleven/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `eleven/upstream/package61_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex` |
| `eleven/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `integer/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/COMPANIONS62_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `integer/upstream/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `integer/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer/upstream/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `integer/upstream/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `integer/upstream/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer/upstream/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer/upstream/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/upstream/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer/upstream/octic30_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `integer/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer/upstream/sextic35_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/sextic35.json` |
| `integer/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive/upstream/compact44_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/upstream/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/upstream/compact44_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive/upstream/package61_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex` |
| `positive/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |

### `71-determinant-guards/` (`con_zfc_calibrated_determinant_guards_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `coefficients/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `coefficients/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine_positive/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/circuit.py` |
| `nine_positive/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/BUILD_RECEIPT.json` |
| `nine_positive/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_positive/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `nine_positive/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine_positive/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `nine_positive/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/K.bin.gz` |
| `nine_positive/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `nine_positive/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MC.bin.gz` |
| `nine_positive/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `nine_positive/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/MF_source.bin.gz` |
| `nine_positive/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `nine_positive/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `nine_positive/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine_positive/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine_positive/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/kernels.json` |
| `nine_positive/data/layout.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/layout.json` |
| `nine_positive/data/order7_majorant_positive_certificate.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/nine/data/order7_majorant_positive_certificate.json` |
| `nine_positive/data/source_system65.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/quartic31/upstream/quartic31_system.json` |
| `nine_positive/rewrite_powers.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/nine/rewrite_powers.py` |
| `nine_positive/upstream59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine_positive/upstream63_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/nine/PROOF.md` |
| `nine_positive/upstream65_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `positive12/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive12/native/COEFFICIENT_BINDING.original.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive12/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive12/native/SOURCE_PINS.original.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive12/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive12/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive12/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive12/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive12/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive12/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive12/source/PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive12/source/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `positive12/source/build12_upstream.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/build12.py` |
| `positive12/source/package61_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex` |
| `positive12/source/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `upstream/34-integer14_coefficients_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/34-integer14_coefficients_sources_WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `upstream/62-sign-and-norm_quartic42_companions_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `upstream/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `upstream/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |

### `72-congruence-sextic/` (`con_zfc_congruence_and_sextic_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer34/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer34/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer34/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer34/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer34/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer34/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer34/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer34/upstream/PARENT_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/SOURCE_PINS.json` |
| `integer34/upstream/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer34/upstream/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer34/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer34/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer34/upstream/polynomial_arithmetic.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_verify44.py` |
| `integer34/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer34/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive13/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive13/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive13/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive13/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive13/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `positive13/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `positive13/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `positive13/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `positive13/native/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive13/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive13/native/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive13/upstream/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `positive13/upstream/COMPACT_PREDECESSOR_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive13/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `positive13/upstream/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive13/upstream/PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `positive13/upstream/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `positive13/upstream/WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive13/upstream/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `provenance/K215_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `provenance/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `provenance/comparison/60-positive-gap.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/60-positive-gap/README.md` |
| `provenance/comparison/61-congruence-carriers.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/README.md` |
| `provenance/comparison/62-sign-and-norm.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/README.md` |
| `provenance/comparison/63-sign-recovery.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/README.md` |
| `provenance/comparison/64-structural-reductions.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/README.md` |
| `provenance/comparison/65-shared-taps.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/README.md` |
| `provenance/comparison/66-gap-congruence.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/README.md` |
| `provenance/comparison/67-oriented-guards.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/README.md` |

### `73-guard-reanchoring/` (`con_zfc_guard_reanchoring.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compact_coefficients/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `compact_coefficients/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `compact_coefficients/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `compact_coefficients/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `compact_coefficients/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `compact_coefficients/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `compact_coefficients/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `compact_coefficients/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `compact_coefficients/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `compact_coefficients/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `compact_coefficients/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `compact_coefficients/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `compact_coefficients/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `compact_coefficients/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `compact_coefficients/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `compact_coefficients/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `compact_coefficients/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `compact_coefficients/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `compact_coefficients/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `compact_coefficients/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `compact_coefficients/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `compact_coefficients/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `compact_coefficients/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `compact_coefficients/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `compact_coefficients/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `compact_coefficients/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `compact_coefficients/native/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `compact_coefficients/upstream/FOURTEEN_GAP_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/fourteen/PROOF.md` |
| `compact_coefficients/upstream/FOURTEEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/50-midpoint11/fourteen/FOURTEEN_PROOF.md` |
| `compact_coefficients/upstream/INTEGRAL_ROOT_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `compact_coefficients/upstream/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `compact_coefficients/upstream/PELL_LEMMAS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `compact_coefficients/upstream/SQUARED_MODULUS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md` |
| `compact_coefficients/upstream/TRANSPORT_SHIFT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/positive/upstream/TRANSPORT_SHIFT_PROOF.original29.md` |
| `compact_coefficients/upstream/positive61/AUDIT12.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/AUDIT12.md` |
| `compact_coefficients/upstream/positive61/PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `compact_coefficients/upstream/positive61/PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `compact_coefficients/upstream/positive61/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `integer34/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer_coefficients/payloads/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer_coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin` |
| `integer_coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `integer_coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin` |
| `integer_coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `integer_coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin` |
| `integer_coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `integer_coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `integer_coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `integer_coefficients/proofs/BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `integer_coefficients/proofs/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer_coefficients/proofs/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `integer_coefficients/proofs/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer_coefficients/proofs/K215_ORDINARY_CALIBRATION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer_coefficients/proofs/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer_coefficients/proofs/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `integer_coefficients/proofs/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `integer_coefficients/proofs/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer_coefficients/proofs/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer_coefficients/proofs/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `integer_coefficients/proofs/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer_coefficients/proofs/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer_coefficients/proofs/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer_coefficients/upstream/source34/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `integer_coefficients/upstream/source34/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer_coefficients/upstream/source34/SOURCE_LEDGER.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/SOURCE_LEDGER.json` |
| `integer_coefficients/upstream/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer_coefficients/upstream/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer_coefficients/upstream/source34/verify_independent.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/verify_independent.py` |
| `integer_coefficients/upstream/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer_coefficients/upstream/source57/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `integer_coefficients/upstream/source64/build_verify41.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_verify41.py` |
| `integer_coefficients/upstream/source64/build_verify44.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_verify44.py` |
| `integer_coefficients/upstream/source64/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer_coefficients/upstream/source64/quartic44.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic44.json` |
| `provenance/61-congruence-carriers_positive_AUDIT12.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/AUDIT12.md` |
| `provenance/61-congruence-carriers_positive_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `provenance/61-congruence-carriers_positive_PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `provenance/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `provenance/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `report.aux` | not staged: TeX build artifact (`*.aux`) |
| `report.fdb_latexmk` | not staged: TeX build artifact (`*.fdb_latexmk`) |
| `report.fls` | not staged: TeX build artifact (`*.fls`) |
| `report.log` | not staged: log file (`*.log`) |
| `report.out` | not staged: TeX build artifact (`*.out`) |
| `report.toc` | not staged: TeX build artifact (`*.toc`) |
| `validation/latex-build.log` | not staged: log file (`*.log`) |
| `validation/latex-final.log` | not staged: log file (`*.log`) |
| `validation/normal/bind_compact_integer34.log` | not staged: log file (`*.log`) |
| `validation/normal/build_integer34.log` | not staged: log file (`*.log`) |
| `validation/normal/build_original_coefficients.log` | not staged: log file (`*.log`) |
| `validation/normal/build_positive12.log` | not staged: log file (`*.log`) |
| `validation/normal/build_positive13.log` | not staged: log file (`*.log`) |
| `validation/normal/check_integer34.log` | not staged: log file (`*.log`) |
| `validation/normal/check_original_coefficients.log` | not staged: log file (`*.log`) |
| `validation/normal/check_positive.log` | not staged: log file (`*.log`) |
| `validation/normal/compact_coefficients.log` | not staged: log file (`*.log`) |
| `validation/normal/compact_integer_adapter.log` | not staged: log file (`*.log`) |
| `validation/normal/reusable_lemmas.log` | not staged: log file (`*.log`) |
| `validation/optimized/bind_compact_integer34.log` | not staged: log file (`*.log`) |
| `validation/optimized/build_integer34.log` | not staged: log file (`*.log`) |
| `validation/optimized/build_original_coefficients.log` | not staged: log file (`*.log`) |
| `validation/optimized/build_positive12.log` | not staged: log file (`*.log`) |
| `validation/optimized/build_positive13.log` | not staged: log file (`*.log`) |
| `validation/optimized/check_integer34.log` | not staged: log file (`*.log`) |
| `validation/optimized/check_original_coefficients.log` | not staged: log file (`*.log`) |
| `validation/optimized/check_positive.log` | not staged: log file (`*.log`) |
| `validation/optimized/compact_coefficients.log` | not staged: log file (`*.log`) |
| `validation/optimized/compact_integer_adapter.log` | not staged: log file (`*.log`) |
| `validation/optimized/reusable_lemmas.log` | not staged: log file (`*.log`) |

### `74-centered-pell-gaps/` (`con-zfc-centered-pell-gaps-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/K.bin.gz` |
| `coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MC.bin.gz` |
| `coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/MF_source.bin.gz` |
| `coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/beta.bin.gz` |
| `upstream/COMPACT44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `upstream/INHERITED_ORDINARY_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `upstream/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `upstream/SOURCE58_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `upstream/SOURCE61_AUDIT12.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/AUDIT12.md` |
| `upstream/SOURCE61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `upstream/SOURCE61_PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `upstream/SOURCE61_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/README.md` |
| `upstream/SOURCE66_COMPARISON.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/report/comparison.tex` |
| `upstream/SOURCE66_METRICS.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/report/metrics.tex` |
| `upstream/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |

### `75-signed-bootstrap/` (`ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `direct/upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `direct/upstream/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `guards/upstream/q41/COMPANIONS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/COMPANIONS_PROOF.md` |
| `guards/upstream/q41/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `guards/upstream/q41/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `guards/upstream/q41/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/SOURCE_PINS.json` |
| `guards/upstream/q41/build_companions.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_companions.py` |
| `guards/upstream/q41/build_verify41.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_verify41.py` |
| `guards/upstream/q41/build_verify44.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/build_verify44.py` |
| `guards/upstream/q41/certificates/COEFFICIENT_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/COEFFICIENT_CHECKS.json` |
| `guards/upstream/q41/certificates/OCTIC31_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/OCTIC31_CHECKS.json` |
| `guards/upstream/q41/certificates/QUARTIC41_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/QUARTIC41_CHECKS.json` |
| `guards/upstream/q41/certificates/QUARTIC41_EXPANSION.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/QUARTIC41_EXPANSION.json` |
| `guards/upstream/q41/certificates/QUARTIC44_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/QUARTIC44_CHECKS.json` |
| `guards/upstream/q41/certificates/SEXTIC36_CHECKS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/certificates/SEXTIC36_CHECKS.json` |
| `guards/upstream/q41/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/K.bin.gz` |
| `guards/upstream/q41/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MC.bin.gz` |
| `guards/upstream/q41/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/payloads/MF_source.bin.gz` |
| `guards/upstream/q41/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/beta.bin.gz` |
| `guards/upstream/q41/octic31.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/octic31.json` |
| `guards/upstream/q41/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `guards/upstream/q41/quartic44.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic44.json` |
| `guards/upstream/q41/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/section.tex` |
| `guards/upstream/q41/sextic36.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/sextic36.json` |
| `guards/upstream/q41/upstream/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `guards/upstream/q41/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `guards/upstream/q41/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `guards/upstream/q41/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `guards/upstream/q41/upstream/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `guards/upstream/q41/upstream/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `guards/upstream/q41/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `guards/upstream/q41/upstream/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `guards/upstream/q41/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `incoming/ConZFC_Gap_Congruence_2026-10-23.zip` | `docs/incoming/ConZFC_Gap_Congruence_2026-10-23.zip (arrival 0c6be9a074)` |
| `incoming/ConZFC_Positive_Gap_2026-10-23.zip` | `docs/incoming/ConZFC_Positive_Gap_2026-10-23.zip (arrival 0c6be9a074)` |
| `incoming/ZFC_Diophantine_Oriented_Guards_2026-10-23.zip` | `docs/incoming/ZFC_Diophantine_Oriented_Guards_2026-10-23.zip (arrival 0c6be9a074)` |
| `incoming/con-zfc-congruence-carriers.zip` | `docs/incoming/con-zfc-congruence-carriers.zip (arrival 0c6be9a074)` |
| `incoming/con-zfc-sign-and-norm.zip` | `docs/incoming/con-zfc-sign-and-norm.zip (arrival 0c6be9a074)` |
| `incoming/con-zfc-sign-recovery-2026-10-23.zip` | `docs/incoming/con-zfc-sign-recovery-2026-10-23.zip (arrival 0c6be9a074)` |
| `incoming/con-zfc-structural-reductions-2026-10-23.zip` | `docs/incoming/con-zfc-structural-reductions-2026-10-23.zip (arrival 0c6be9a074)` |
| `incoming/con_zfc_shared_taps_carriers_2026-10-23.zip` | `docs/incoming/con_zfc_shared_taps_carriers_2026-10-23.zip (arrival 0c6be9a074)` |
| `low_degree/dag.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/dag.py` |
| `low_degree/inherited/ADAPTIVE_CARRIER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/INDEPENDENT_PROOF_AUDIT.md` |
| `low_degree/inherited/AUDIT12.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/AUDIT12.md` |
| `low_degree/inherited/PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `low_degree/inherited/PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `low_degree/inherited/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `mixed_source/parent_source.json` | `Computability/DiophantineConsistency/data/split59/parent_source.json` |
| `review/baseline/ConZFC_Gap_Congruence_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/ConZFC_Positive_Gap_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/NATIVE_PELL_STEP_DOWN.md` | `Computability/DiophantineConsistency/NATIVE_PELL_STEP_DOWN.md` |
| `review/baseline/SPLIT_SOURCE_EXISTENCE.md` | `Computability/DiophantineConsistency/SPLIT_SOURCE_EXISTENCE.md` |
| `review/baseline/SplitNineSource59.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitNineSource59.lean` |
| `review/baseline/SplitSourceExistence.lean` | `Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitSourceExistence.lean` |
| `review/baseline/ZFC_Diophantine_Oriented_Guards_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con-zfc-congruence-carriers.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con-zfc-sign-and-norm.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con-zfc-sign-recovery-2026-10-23.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/VERIFICATION.json` |
| `review/baseline/con-zfc-structural-reductions-2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con_zfc_shared_taps_carriers_2026-10-23.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `review/baseline/con_zfc_shared_taps_carriers_2026-10-23.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/VERIFICATION.json` |
| `review/formal/NATIVE_PELL_STEP_DOWN.md` | `Computability/DiophantineConsistency/NATIVE_PELL_STEP_DOWN.md` |
| `review/formal/SPLIT_SOURCE_EXISTENCE.md` | `Computability/DiophantineConsistency/SPLIT_SOURCE_EXISTENCE.md` |
| `review/latest/CANDIDATE.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/README.md` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `review/baseline/COUNT.log` | not staged: log file (`*.log`) |
| `review/baseline/PARETO.log` | not staged: log file (`*.log`) |
| `review/interfaces/SHA256SUMS` | not staged: checksum ledger |
| `review/positive/bindings_normal.log` | not staged: log file (`*.log`) |
| `review/positive/bindings_optimized.log` | not staged: log file (`*.log`) |
| `review/positive/low_degree12_normal.log` | not staged: log file (`*.log`) |
| `review/positive/low_degree12_optimized.log` | not staged: log file (`*.log`) |
| `review/positive/low_degree13_normal.log` | not staged: log file (`*.log`) |
| `review/positive/low_degree13_optimized.log` | not staged: log file (`*.log`) |
| `review/positive/normal.log` | not staged: log file (`*.log`) |
| `review/positive/optimized.log` | not staged: log file (`*.log`) |
| `review/positive/portability.log` | not staged: log file (`*.log`) |

## Placement record: batch 227 (wave 11)

Intake record, not a delivered file. The thirty-six archives that arrived in
the seventeen commits `c1a102936a` (23 October 2026, 18:35) to `e13c748234`
(24 October 2026, 12:14), all titled "Con(ZFC) in Diophantine form", were
extracted straight from the committed ZIPs into numbered directories 76–110,
in arrival order (archive-name order within one commit), with the single
wrapper directory removed. Nothing was edited and nothing was run at intake.

**Waves 5–10 are kept.** By Vladimir's direction, wave 11 is placed beside
them (sources 31–75), not instead of them; this section is appended to the
earlier records above.

One archive is not a directory. `ZFC_Diophantine_Centered_Compression_2026-10-24_Dependency.zip`
(arrival `922185752d`) wraps a single member, a byte copy of
`ZFC_Diophantine_Joint_Guards_2026-10-24.zip` (arrival `c1a102936a`, placed
as `77-joint-guards/`); it is retired without a directory. `report.zip`
(arrival `c1a102936a`) holds one TeX file and no wrapper; it is `80-twelve-manuscript/`.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted. This includes copies of the
  wave-5 to wave-10 files of this report, which stay in the tree, and the
  many bundled copies of this batch's own siblings (`upstream/`, `inherited/`,
  `baseline/` folders). The tables below name the shortest repository path
  holding the same bytes. Licence, notice and attribution files are always
  kept. **Refinement in `240bf9e422`'s follow-up:** the active research
  session copies arriving packages into `Computability/DiophantineConsistency/`
  outside this report (its `candidates/`, `research/`, `tools/` and worktree
  copies), and rewrites them. A member whose only repository copies lie there
  is kept, so that every package stays self-contained; the first placement
  had omitted 1,119 such members (1,108 staged files), among them headline equation files, and
  they were restored in the next commit. Only matches to this report, to the
  arrival archives and to stable repository files (Lean sources, the Hilbert
  Tenth project, Busy Beaver research) are still omitted.
  A member equal to an arrival ZIP (77 bundles wave-10's Signed
  Bootstrap archive, 90 and 110 bundle siblings of this batch) is mapped to
  the earliest arrival commit holding it, because this placement retires the
  `docs/incoming/` paths.
- **Checksum ledgers, logs and TeX build artifacts.** `SHA256SUMS*`, `*.log`
  and TeX auxiliaries are excluded by the root `.gitignore`; they were not
  verified.

To rerun a package, extract its archive from its arrival commit into a
scratch directory and run it there:

```sh
git show <arrival>:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Arrival | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---|---:|---:|---:|---:|---|
| `76-structural-round11/` | `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | `c1a102936a` | 366 | 177 | 189 | 0 | `con-zfc-structural-reductions-round11/` |
| `77-joint-guards/` | `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | `c1a102936a` | 301 | 211 | 89 | 1 | `ZFC_Diophantine_Joint_Guards/` |
| `78-budget-centering/` | `con-zfc-budget-and-centering-2026-10-23.zip` | `c1a102936a` | 113 | 87 | 26 | 0 | `con-zfc-budget-and-centering-2026-10-23/` |
| `79-radical-guard-descent/` | `con-zfc-radical-guard-descent-2026-10-23.zip` | `c1a102936a` | 170 | 102 | 68 | 0 | `con-zfc-cross-guard-descent-2026-10-23/` |
| `80-twelve-manuscript/` | `report.zip` | `c1a102936a` | 1 | 1 | 0 | 0 | none |
| `81-centered-pell-norms/` | `con-zfc-centered-pell-norms.zip` | `9a33342a03` | 142 | 87 | 55 | 0 | `con-zfc-centered-pell-norms/` |
| `82-pell-congruences/` | `con_zfc_pell_congruences_2026-10-23.zip` | `eae4f1952b` | 230 | 131 | 98 | 1 | `con_zfc_pell_congruences_2026-10-23/` |
| `83-polynomial-shears/` | `ConZFC_Polynomial_Shears_2026-10-23.zip` | `440dd03ab8` | 175 | 128 | 47 | 0 | `con_zfc_polynomial_shears/` |
| `84-radical-residue/` | `con-zfc-radical-residue-2026-10-23.zip` | `440dd03ab8` | 108 | 81 | 27 | 0 | `con-zfc-radical-residue-2026-10-23/` |
| `85-saturation-projection/` | `con-zfc-saturation-and-projection-2026-10-23.zip` | `440dd03ab8` | 235 | 177 | 58 | 0 | `con-zfc-saturation-and-projection-2026-10-23/` |
| `86-saturated-certificates/` | `ConZFC_Saturated_Certificates_2026-10-24.zip` | `d42be5cd87` | 255 | 155 | 100 | 0 | `con-zfc-saturated-certificates-2026-10-24/` |
| `87-direct-centered-round12/` | `ConZFC_Direct_Centered_Round12_2026-10-24.zip` | `a83816984d` | 319 | 200 | 119 | 0 | `con-zfc-direct-and-centered-round12/` |
| `88-root-fusion13/` | `ConZFC_13_Integer_Norms_2026-10-24.zip` | `751bc067e2` | 93 | 67 | 25 | 1 | `con-zfc-root-fusion-2026-10-24/` |
| `89-shared-certificates/` | `ConZFC_Shared_Certificates_2026-10-24.zip` | `751bc067e2` | 116 | 88 | 28 | 0 | `con_zfc_shared_certificates/` |
| `90-fixed-prime-radicals/` | `ConZFC_FixedPrime_Radicals_2026-10-23.zip` | `1072d31072` | 104 | 60 | 44 | 0 | `con-zfc-padic-compression/` |
| `91-prime-separation13/` | `ConZFC_Prime_Separation_13_Integer_2026-10-23.zip` | `f6b6c83b1c` | 176 | 112 | 63 | 1 | `con_zfc_prime_separation_2026-10-23/` |
| `92-parity-norms/` | `con-zfc-parity-norms-2026-10-23.zip` | `f6b6c83b1c` | 317 | 203 | 112 | 2 | `con-zfc-parity-norms-2026-10-23/` |
| `93-parity-pell-witnesses/` | `con-zfc-parity-norms-2026-10-23 (2).zip` | `e2b2f16765` | 235 | 192 | 43 | 0 | `con-zfc-parity-norms/` |
| `94-direct-projection7617/` | `ConZFC_Direct_Projection_7617.zip` | `b594a5e988` | 75 | 58 | 17 | 0 | `con_zfc_direct_projection/` |
| `95-synchronized-certificates/` | `ConZFC_Synchronized_Certificates_2026-10-24.zip` | `8f8fac484b` | 89 | 79 | 7 | 3 | `con_zfc_synchronized_certificates/` |
| `96-batched-certificates/` | `con_zfc_batched_certificates_2026-10-23.zip` | `8f8fac484b` | 233 | 197 | 31 | 5 | `con-zfc-batched-certificates/` |
| `97-twelve-interpolation/` | `ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip` | `85ae407001` | 138 | 106 | 26 | 6 | `con_zfc_trace_and_interpolation/` |
| `98-congruence-certificates/` | `ConZFC_Congruence_Certificates_2026-10-24.zip` | `a6269e4da6` | 205 | 150 | 55 | 0 | `con_zfc_congruence_certificates/` |
| `99-shared-pell608/` | `ConZFC_Shared_Pell_608_2026-10-23.zip` | `a6269e4da6` | 79 | 74 | 5 | 0 | `con-zfc-shared-pell-2026-10-23/` |
| `100-quartics407-888/` | `ConZFC_407_888_Quartics_2026-10-24.zip` | `3635835b1e` | 130 | 123 | 6 | 1 | `ConZFC_407_888_Quartics/` |
| `101-constructive-reductions/` | `ConZFC_Constructive_Reductions_2026-10-23.zip` | `3635835b1e` | 339 | 246 | 93 | 0 | `ConZFC_Constructive_Reductions_2026-10-23/` |
| `102-direct-quartics3776/` | `ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip` | `3635835b1e` | 101 | 91 | 9 | 1 | `conzfc_signed_quartic/` |
| `103-shared-pell1873/` | `ConZFC_Shared_Pell_1873.zip` | `3635835b1e` | 93 | 75 | 17 | 1 | `con_zfc_batched_pell/` |
| `104-valuation-signed/` | `ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip` | `3635835b1e` | 302 | 235 | 62 | 5 | `ConZFC_Valuation_and_Signed_Certificates/` |
| `105-bootstrap-certificates/` | `ConZFC_Bootstrap_Certificates_2026-10-24.zip` | `e13c748234` | 328 | 263 | 65 | 0 | `con-zfc-bootstrap-certificates/` |
| `106-compact-certificates-round13/` | `ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.zip` | `e13c748234` | 399 | 294 | 104 | 1 | `ConZFC_Compact_Proof_Certificates_Round13_2026-10-24/` |
| `107-dyadic-pell/` | `ConZFC_Dyadic_Pell_Reductions_2026-10-23.zip` | `e13c748234` | 68 | 59 | 8 | 1 | `ConZFC_Dyadic_Pell_Reductions_2026-10-23/` |
| `108-pell-residues/` | `ConZFC_Pell_Residues_2026-10-23.zip` | `e13c748234` | 214 | 185 | 27 | 2 | `ConZFC_Pell_Residues/` |
| `109-valuations-centered/` | `ConZFC_Valuations_and_Centered_Certificates.zip` | `e13c748234` | 287 | 231 | 55 | 1 | `ConZFC_Valuations_and_Centered_Certificates/` |
| `110-budget-interpolation/` | `ZFC_Diophantine_Budget_Interpolation_2026-10-24.zip` | `e13c748234` | 849 | 566 | 264 | 19 | `ZFC_Diophantine_Budget_Interpolation/` |
| none (duplicate archive) | `ZFC_Diophantine_Centered_Compression_2026-10-24_Dependency.zip` | `922185752d` | 1 | 0 | 1 | 0 | none |

Total: 7386 members = 5291 staged + 2043 omitted copies + 52 ignored.

### `76-structural-round11/` (`ConZFC_Structural_Reductions_Round11_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `commutative/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |
| `inherited/round10/calculus_api/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/SOURCE_PINS.json` |
| `inherited/round10/calculus_api/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `inherited/round10/calculus_api/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `inherited/round10/calculus_api/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `inherited/round10/direct/AFFINE_PRODUCT_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/AFFINE_PRODUCT_CERTIFICATES.md` |
| `inherited/round10/direct/COMMUTATIVE_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/COMMUTATIVE_CERTIFICATES.md` |
| `inherited/round10/free_carrier_audit/strengthened_lucas.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/report/lucas.tex` |
| `inherited/round10/integer_source/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `inherited/round10/integer_source/25-hybrid12_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/25-hybrid12_COEFFICIENT_BINDING.json` |
| `inherited/round10/integer_source/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `inherited/round10/integer_source/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `inherited/round10/integer_source/27-wave4_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/27-wave4_COEFFICIENT_BINDING.json` |
| `inherited/round10/integer_source/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `inherited/round10/integer_source/COMPANIONS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `inherited/round10/integer_source/PRIME_PADDING.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `inherited/round10/integer_source/Q42_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/PROOF.md` |
| `inherited/round10/integer_source/SOURCE34_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json` |
| `inherited/round10/integer_source/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `inherited/round10/integer_source/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `inherited/round10/integer_source/octic30.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `inherited/round10/integer_source/quartic42_x_square.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/quartic42_x_square.json` |
| `inherited/round10/norm/final10/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/PROOF.md` |
| `inherited/round10/packing/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/PROOF.md` |
| `low_degree_audit/inherited_interfaces/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `low_degree_audit/inherited_interfaces/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `low_degree_audit/inherited_interfaces/package61_PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `low_degree_audit/inherited_interfaces/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `lucas/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `lucas/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `lucas/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `lucas/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `lucas/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `lucas/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `lucas/data/code.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_code.json` |
| `lucas/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `lucas/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_kernels.json` |
| `lucas/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `lucas/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `lucas/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `lucas/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `lucas/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `lucas/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `lucas/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `lucas/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `lucas/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `lucas/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `lucas/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `lucas/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `lucas/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `lucas/provenance/BASELINE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/signed/SOURCE_PINS.json` |
| `lucas/provenance/PACKING_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/SOURCE_PINS.json` |
| `lucas/provenance/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `lucas/provenance/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `lucas/provenance/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `lucas/provenance/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `lucas/provenance/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `lucas_audit/inherited/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `lucas_audit/inherited/data/code.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_code.json` |
| `lucas_audit/inherited/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_kernels.json` |
| `lucas_audit/inherited/integer10.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/integer10.json` |
| `lucas_h1868/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `lucas_h1868/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `lucas_h1868/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `lucas_h1868/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `lucas_h1868/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `lucas_h1868/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `lucas_h1868/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `lucas_h1868/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `lucas_h1868/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `lucas_h1868/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `lucas_h1868/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `lucas_h1868/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `lucas_h1868/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `lucas_h1868/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `lucas_h1868/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `lucas_h1868/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `lucas_h1868/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `lucas_h1868/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `lucas_h1868/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `lucas_h1868/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `lucas_h1868/provenance/BASELINE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/signed/SOURCE_PINS.json` |
| `lucas_h1868/provenance/PACKING_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/SOURCE_PINS.json` |
| `lucas_h1868/provenance/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `lucas_h1868/provenance/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `lucas_h1868/provenance/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `lucas_h1868/provenance/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `lucas_h1868/provenance/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `packing/certified/prior_kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_kernels.json` |
| `packing/certified/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `packing/factor_gap/prior_source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `positive/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/native/FETCH_PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/FETCH_PROVENANCE.json` |
| `positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positivity/coefficients/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `positivity/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positivity/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `positivity/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `positivity/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `positivity/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `positivity/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `positivity/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `positivity/coefficients/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `positivity/coefficients/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `positivity/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positivity/inherited/34-integer14_coefficients_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `positivity/inherited/34-integer14_coefficients_sources_WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `positivity/inherited/62-sign-and-norm_quartic42_companions_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `positivity/inherited/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `positivity/inherited/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `positivity/inherited/ACTIVE_FORMALIZATION_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/baseline/active_research_README.md` |
| `positivity/inherited/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `positivity/inherited/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `positivity/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `positivity/inherited/ORIENTATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `positivity/inherited/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `positivity/inherited/SEXTIC_PIVOT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/integer34/PROOF_SEXTIC34.md` |
| `positivity/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `positivity/inherited/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `positivity/inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `positivity/inherited/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `review/packages/69-cones-pell/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/README.md` |
| `review/packages/69-cones-pell/integer/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/PROOF.md` |
| `review/packages/69-cones-pell/integer/octic27.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/octic27.json` |
| `review/packages/69-cones-pell/integer/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/quartic38.json` |
| `review/packages/69-cones-pell/integer/sextic32.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/sextic32.json` |
| `review/packages/69-cones-pell/positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `review/packages/69-cones-pell/positive/equation.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/equation.json` |
| `review/packages/70-residue-orientation/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/README.md` |
| `review/packages/70-residue-orientation/eleven/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `review/packages/70-residue-orientation/eleven/p11_positive_degree325.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/p11_positive_degree325.json` |
| `review/packages/70-residue-orientation/integer/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `review/packages/70-residue-orientation/integer/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `review/packages/70-residue-orientation/positive/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `review/packages/71-determinant-guards/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/README.md` |
| `review/packages/71-determinant-guards/integer_forms/octic27.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/octic27.json` |
| `review/packages/71-determinant-guards/integer_forms/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `review/packages/71-determinant-guards/integer_forms/sextic32.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/sextic32.json` |
| `review/packages/71-determinant-guards/nine_positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `review/packages/71-determinant-guards/nine_positive/generated/composed9_positive.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `review/packages/71-determinant-guards/positive12/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/positive12/PROOF.md` |
| `review/packages/71-determinant-guards/proofs/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `review/packages/72-congruence-sextic/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/README.md` |
| `review/packages/72-congruence-sextic/integer34/PROOF_SEXTIC34.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/integer34/PROOF_SEXTIC34.md` |
| `review/packages/72-congruence-sextic/integer34/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/integer34/sextic34.json` |
| `review/packages/72-congruence-sextic/positive13/PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/positive13/PROOF13.md` |
| `review/packages/72-congruence-sextic/positive13/p13_degree28.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/positive13/p13_degree28.json` |
| `review/packages/72-congruence-sextic/positive14/PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/positive14/PROOF14.md` |
| `review/packages/72-congruence-sextic/positive14/p14_degree24.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/positive14/p14_degree24.json` |
| `review/packages/73-guard-reanchoring/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/README.md` |
| `review/packages/73-guard-reanchoring/integer34/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/integer34/PROOF.md` |
| `review/packages/73-guard-reanchoring/integer34/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/integer34/sextic34.json` |
| `review/packages/73-guard-reanchoring/positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/positive/PROOF.md` |
| `review/packages/73-guard-reanchoring/positive/p13_degree30.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/positive/p13_degree30.json` |
| `review/packages/73-guard-reanchoring/research/junk_conservative_syntax.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/research/junk_conservative_syntax.md` |
| `review/packages/73-guard-reanchoring/research/pell_jet_carrier.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/research/pell_jet_carrier.md` |
| `review/packages/74-centered-pell-gaps/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/README.md` |
| `review/packages/74-centered-pell-gaps/circuits/positive12_product.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/circuits/positive12_product.json` |
| `review/packages/74-centered-pell-gaps/positive13/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/positive13/PROOF.md` |
| `review/packages/74-centered-pell-gaps/report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/report.tex` |
| `review/packages/75-signed-bootstrap/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/README.md` |
| `review/packages/75-signed-bootstrap/certificates/INERT_PRIME_CLOSURE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/certificates/INERT_PRIME_CLOSURE.md` |
| `review/packages/75-signed-bootstrap/direct/BOUNDARY_THEOREM.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/direct/BOUNDARY_THEOREM.md` |
| `review/packages/75-signed-bootstrap/guards/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `review/packages/75-signed-bootstrap/guards/signed34_sextic.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/signed34_sextic.json` |
| `review/packages/75-signed-bootstrap/low_degree/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/low_degree/PROOF.md` |

### `77-joint-guards/` (`ZFC_Diophantine_Joint_Guards_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `baseline/ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/ZFC_Diophantine_Signed_Bootstrap_2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-centered-pell-gaps-2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-centered-pell-gaps-2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-cones-pell-2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-cones-pell-2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-residue-orientation-root-transfer-2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-residue-orientation-root-transfer-2026-10-23.normal.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/certificates/ROOT_NORMAL.json` |
| `baseline/con-zfc-residue-orientation-root-transfer-2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con-zfc-residue-orientation-root-transfer-2026-10-23.optimized.stdout.txt` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/certificates/ROOT_OPTIMIZED.json` |
| `baseline/con_zfc_calibrated_determinant_guards_2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con_zfc_calibrated_determinant_guards_2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con_zfc_congruence_and_sextic_2026-10-23.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con_zfc_congruence_and_sextic_2026-10-23.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con_zfc_guard_reanchoring.normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/con_zfc_guard_reanchoring.optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `certificates/upstream/INERT_PRIME_CLOSURE_WAVE10.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/certificates/INERT_PRIME_CLOSURE.md` |
| `circuits/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `guards/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `guards/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `guards/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `guards/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `guards/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `guards/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `guards/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `guards/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `guards/upstream/SIGNED_POWER_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `guards/upstream/cone/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/PROOF.md` |
| `guards/upstream/cone/REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/REVIEW.md` |
| `guards/upstream/cone/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/SOURCE_PINS.json` |
| `guards/upstream/determinant/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `guards/upstream/determinant/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/SOURCE_PINS.json` |
| `guards/upstream/residue/INDEPENDENT_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/INDEPENDENT_REVIEW.md` |
| `guards/upstream/residue/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `guards/upstream/residue/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `guards/upstream/residue/dependencies/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `guards/upstream/residue/dependencies/COMPANIONS62_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `guards/upstream/residue/dependencies/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `guards/upstream/residue/dependencies/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `guards/upstream/residue/dependencies/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `guards/upstream/residue/dependencies/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `guards/upstream/residue/dependencies/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `guards/upstream/residue/dependencies/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `guards/upstream/residue/dependencies/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `guards/upstream/residue/dependencies/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `guards/upstream/residue/dependencies/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `guards/upstream/residue/dependencies/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `guards/upstream/residue/dependencies/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `guards/upstream/residue/dependencies/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `guards/upstream/residue/dependencies/octic30_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `guards/upstream/residue/dependencies/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `guards/upstream/residue/dependencies/sextic35_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/sextic35.json` |
| `guards/upstream/residue/dependencies/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `guards/upstream/residue/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `guards/upstream/residue/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `guards/upstream/residue/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `guards/upstream/residue/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `guards/upstream/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `guards/upstream/source34/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `guards/upstream/source34/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `guards/upstream/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `incoming/ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.zip` | `docs/incoming/ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip` | `docs/incoming/ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con-zfc-centered-pell-gaps-2026-10-23.zip` | `docs/incoming/con-zfc-centered-pell-gaps-2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con-zfc-cones-pell-2026-10-23.zip` | `docs/incoming/con-zfc-cones-pell-2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con-zfc-residue-orientation-root-transfer-2026-10-23.zip` | `docs/incoming/con-zfc-residue-orientation-root-transfer-2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con_zfc_calibrated_determinant_guards_2026-10-23.zip` | `docs/incoming/con_zfc_calibrated_determinant_guards_2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con_zfc_congruence_and_sextic_2026-10-23.zip` | `docs/incoming/con_zfc_congruence_and_sextic_2026-10-23.zip (arrival 9513bd88ce)` |
| `incoming/con_zfc_guard_reanchoring.zip` | `docs/incoming/con_zfc_guard_reanchoring.zip (arrival 9513bd88ce)` |
| `pell/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/SOURCE_PINS.json` |
| `pell/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `pell/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `pell/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `pell/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `pell/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `pell/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `pell/upstream/69-cones-pell__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `pell/upstream/70-residue-orientation__eleven__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `pell/upstream/74-centered-pell-gaps__research__CENTERED12_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/research/CENTERED12_AUDIT.md` |
| `pell/upstream/compact44_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `pell/upstream/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `pell/upstream/compact44_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `pell/upstream/package52_Y_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `pell/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `pell/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `pell/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `pell/upstream/source70_ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/coefficients/ACTIVE_BINDING.json` |
| `pell/upstream/source70_weighted_carrier.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `SHA256SUMS.json` | not staged: checksum ledger |

### `78-budget-centering/` (`con-zfc-budget-and-centering-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer/coefficients/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `integer/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/coefficients/recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/polynomial.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |
| `integer/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer/upstream/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/upstream/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `positive/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/eleven/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `positive/upstream/PROOF11_original.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive/upstream/PROOF12_original.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `positive/upstream/compact44_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |

### `79-radical-guard-descent/` (`con-zfc-radical-guard-descent-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `alternative/upstream/AFFINE_PRODUCT_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/AFFINE_PRODUCT_CERTIFICATES.md` |
| `alternative/upstream/COMMUTATIVE_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/COMMUTATIVE_CERTIFICATES.md` |
| `alternative/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `integer/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/coefficients/UPSTREAM_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `integer/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/polynomial.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |
| `integer/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer/upstream/source34_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/source64_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/source64_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/source68_PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer/upstream/source71_DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/source75_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/review/MATHEMATICAL_REVIEW.md` |
| `integer/upstream/source75_SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `nine_positive/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/circuit.py` |
| `nine_positive/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine_positive/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine_positive/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_positive/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `nine_positive/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `nine_positive/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine_positive/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `nine_positive/coefficients/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `nine_positive/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine_positive/coefficients/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `nine_positive/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine_positive/coefficients/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `nine_positive/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine_positive/coefficients/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `nine_positive/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine_positive/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `nine_positive/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `nine_positive/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `nine_positive/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine_positive/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine_positive/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/kernels.json` |
| `nine_positive/data/layout.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/layout.json` |
| `nine_positive/independent/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `nine_positive/upstream/nine71.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `nine_positive/upstream/nine71_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `nine_positive/upstream/ratio59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine_positive/upstream/source65_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `positive11/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive11/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive11/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive11/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive11/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `positive11/native_recipe/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive11/native_recipe/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive11/native_recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive11/native_recipe/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive11/upstream/44-b4-sparse__native__COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive11/upstream/61-congruence-carriers__positive__SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `positive11/upstream/69-cones-pell__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `positive11/upstream/70-residue-orientation__eleven__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive11/upstream/70-residue-orientation__eleven__build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/build.py` |
| `positive11/upstream/70-residue-orientation__eleven__independent_audit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/independent_audit.py` |
| `positive11/upstream/70-residue-orientation__eleven__p11_positive_degree325.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/p11_positive_degree325.json` |
| `positive11/upstream/70-residue-orientation__positive__section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |

### `81-centered-pell-norms/` (`con-zfc-centered-pell-norms.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `coefficients/recipe/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `coefficients/recipe/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `coefficients/recipe/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `coefficients/recipe/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `coefficients/recipe/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `coefficients/recipe/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `coefficients/recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `coefficients/recipe/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `coefficients/recipe/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `coefficients/recipe/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `coefficients/recipe/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `coefficients/recipe/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/recipe/native_report.pdf` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.pdf` |
| `coefficients/recipe/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `coefficients/recipe/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `coefficients/recipe/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `coefficients/recipe/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `coefficients/recipe/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `coefficients/recipe/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `coefficients/recipe/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `coefficients/recipe/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `coefficients/recipe/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `coefficients/recipe/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `coefficients/recipe/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `coefficients/recipe/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `coefficients/recipe/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/recipe/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `coefficients/recipe/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `coefficients/recipe/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `integer/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/polynomial.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |
| `integer/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer/upstream/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `integer/upstream/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer/upstream/signed34_sextic.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/signed34_sextic.json` |
| `integer/upstream/signed40_sextic.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/signed40_sextic.json` |
| `positive11/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `positive11/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `provenance/source61_signed_index.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `provenance/source69_pell_descent.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `provenance/source70_eleven_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `provenance/source70_weighted_carrier.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |

### `82-pell-congruences/` (`con_zfc_pell_congruences_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `nine_full_radical/circuit_helper.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `nine_full_radical/upstream/31-sun10/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine_full_radical/upstream/31-sun10/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `nine_full_radical/upstream/31-sun10/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `nine_full_radical/upstream/31-sun10/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine_full_radical/upstream/31-sun10/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `nine_full_radical/upstream/31-sun10/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine_full_radical/upstream/31-sun10/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine_full_radical/upstream/31-sun10/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine_full_radical/upstream/31-sun10/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine_full_radical/upstream/31-sun10/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `nine_full_radical/upstream/31-sun10/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `nine_full_radical/upstream/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `nine_full_radical/upstream/31-sun10/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine_full_radical/upstream/31-sun10/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `nine_full_radical/upstream/59-degree-separated/nine_free_adjunct/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine_full_radical/upstream/65-shared-taps/nine/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `nine_full_radical/upstream/65-shared-taps/nine/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/kernels.json` |
| `nine_full_radical/upstream/65-shared-taps/nine/data/layout.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/layout.json` |
| `nine_full_radical/upstream/71-determinant-guards/nine_positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `nine_full_radical/upstream/71-determinant-guards/nine_positive/PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROVENANCE.json` |
| `nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive_degree.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_natural_degree.json` |
| `positive/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `positive/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `positive/native/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positive/upstream/package52_Y_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `positive/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `positive/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `positive/upstream/source69_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `positive/upstream/source69_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/report/report.tex` |
| `positive/upstream/source70_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive/upstream/source70_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/section.tex` |
| `positive/upstream/source70_weighted_source.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `positive/upstream/source72_signed_lemma.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/report.tex` |
| `positive/upstream/source74_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/report.tex` |
| `SHA256SUMS` | not staged: checksum ledger |

### `83-polynomial-shears/` (`ConZFC_Polynomial_Shears_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `alternative/selector/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |
| `calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `integer/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `norm10/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `norm10/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `norm10/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `norm10/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `norm10/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `norm10/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `norm10/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `norm10/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `norm10/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `norm10/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `norm10/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `norm10/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `norm10/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `norm10/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `norm10/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `norm10/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `norm10/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `norm10/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `norm10/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `norm10/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `positive11/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive11/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive11/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive11/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive11/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `positive11/native_recipe/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive11/native_recipe/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive11/native_recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive11/native_recipe/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive11/upstream/44-b4-sparse__native__COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive11/upstream/61-congruence-carriers__positive__SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `positive11/upstream/69-cones-pell__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `positive11/upstream/70-residue-orientation__eleven__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive11/upstream/70-residue-orientation__eleven__build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/build.py` |
| `positive11/upstream/70-residue-orientation__eleven__independent_audit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/independent_audit.py` |
| `positive11/upstream/70-residue-orientation__eleven__p11_positive_degree325.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/p11_positive_degree325.json` |
| `positive11/upstream/70-residue-orientation__positive__section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |

### `84-radical-residue/` (`con-zfc-radical-residue-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `integer/upstream/pell__upstream__69-cones-pell__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `ten_positive/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `ten_positive/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `ten_positive/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `ten_positive/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `ten_positive/upstream/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `ten_positive/upstream/K215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `ten_positive/upstream/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `ten_positive/upstream/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `ten_positive/upstream/compact44_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `ten_positive/upstream/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `ten_positive/upstream/compact44_recipe.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `ten_positive/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `ten_positive/upstream/kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `ten_positive/upstream/normalized_source61.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `ten_positive/upstream/source36_BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `ten_positive/upstream/source36_FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `ten_positive/upstream/source36_ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `ten_positive/upstream/source61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `ten_positive/upstream/source61_PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |

### `85-saturation-projection/` (`con-zfc-saturation-and-projection-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer/upstream/circuits/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `integer/upstream/guards/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/upstream/guards/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/upstream/guards/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/upstream/guards/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `integer/upstream/guards/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `integer/upstream/guards/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/upstream/guards/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/upstream/guards/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/upstream/guards/upstream/SIGNED_POWER_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `integer/upstream/guards/upstream/cone/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/PROOF.md` |
| `integer/upstream/guards/upstream/cone/REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/REVIEW.md` |
| `integer/upstream/guards/upstream/cone/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/SOURCE_PINS.json` |
| `integer/upstream/guards/upstream/determinant/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/guards/upstream/determinant/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/SOURCE_PINS.json` |
| `integer/upstream/guards/upstream/residue/INDEPENDENT_REVIEW.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/INDEPENDENT_REVIEW.md` |
| `integer/upstream/guards/upstream/residue/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `integer/upstream/guards/upstream/residue/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `integer/upstream/guards/upstream/residue/dependencies/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/guards/upstream/residue/dependencies/COMPANIONS62_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `integer/upstream/guards/upstream/residue/dependencies/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `integer/upstream/guards/upstream/residue/dependencies/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer/upstream/guards/upstream/residue/dependencies/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/upstream/guards/upstream/residue/dependencies/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `integer/upstream/guards/upstream/residue/dependencies/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `integer/upstream/guards/upstream/residue/dependencies/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/guards/upstream/residue/dependencies/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/guards/upstream/residue/dependencies/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer/upstream/guards/upstream/residue/dependencies/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer/upstream/guards/upstream/residue/dependencies/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/upstream/guards/upstream/residue/dependencies/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/upstream/guards/upstream/residue/dependencies/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer/upstream/guards/upstream/residue/dependencies/octic30_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/octic30.json` |
| `integer/upstream/guards/upstream/residue/dependencies/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `integer/upstream/guards/upstream/residue/dependencies/sextic35_parent.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/sextic35.json` |
| `integer/upstream/guards/upstream/residue/dependencies/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/upstream/guards/upstream/residue/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `integer/upstream/guards/upstream/residue/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `integer/upstream/guards/upstream/residue/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `integer/upstream/guards/upstream/residue/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `integer/upstream/guards/upstream/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/upstream/guards/upstream/source34/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/upstream/guards/upstream/source34/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/upstream/guards/upstream/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/upstream/source73_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/report.tex` |
| `nine/coefficients/compact_tuple/K.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/K.bin.gz` |
| `nine/coefficients/compact_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MC.bin.gz` |
| `nine/coefficients/compact_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MF_source.bin.gz` |
| `nine/coefficients/compact_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/data/H2082/kernels.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/kernels.json` |
| `nine/data/H2082/layout.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/layout.json` |
| `nine/data/H2082/source.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/source.json` |
| `nine/data/parent_source.json` | `Computability/DiophantineConsistency/data/split59/parent_source.json` |
| `nine/provenance/SOURCE31_ADAPTER.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/SOURCE31_ADAPTER.md` |
| `nine/provenance/interface_proof.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/interface_proof.md` |
| `nine/provenance/nine-PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/nine-PROOF.md` |
| `nine/provenance/source-GAP_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/source-GAP_SOURCE_PROOF.md` |
| `provenance/73-guard-reanchoring-report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/report.tex` |

### `86-saturated-certificates/` (`ConZFC_Saturated_Certificates_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `integer/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/upstream/34-integer14_coefficients_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer/upstream/ORIENTATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `integer/upstream/RATIONAL_PELL_DESCENT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `integer/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer/upstream/polynomial_original.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |
| `nine/baseline/ProductPell.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/audit/ProductPell.lean.txt` |
| `nine/baseline/compact2082/coefficients/compact_tuple/K.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/K.bin.gz` |
| `nine/baseline/compact2082/coefficients/compact_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MC.bin.gz` |
| `nine/baseline/compact2082/coefficients/compact_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MF_source.bin.gz` |
| `nine/baseline/compact2082/coefficients/compact_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/baseline/compact2082/data/H2082/kernels.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/kernels.json` |
| `nine/baseline/compact2082/data/H2082/layout.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/layout.json` |
| `nine/baseline/compact2082/data/H2082/source.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/source.json` |
| `nine/baseline/compact2082/data/parent_source.json` | `Computability/DiophantineConsistency/data/split59/parent_source.json` |
| `nine/baseline/compact2082/provenance/SOURCE31_ADAPTER.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/SOURCE31_ADAPTER.md` |
| `nine/baseline/compact2082/provenance/interface_proof.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/interface_proof.md` |
| `nine/baseline/compact2082/provenance/nine-PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/nine-PROOF.md` |
| `nine/baseline/compact2082/provenance/source-GAP_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/source-GAP_SOURCE_PROOF.md` |
| `nine/baseline/h1868/prior_kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_kernels.json` |
| `nine/baseline/inherited/nine71.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `nine/baseline/inherited/nine71_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `nine/baseline/inherited/ratio59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/baseline/inherited/source65_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/circuit.py` |
| `nine/data/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `nine/fixed/h1868/base_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/base_scale.bin.gz` |
| `nine/fixed/h1868/c000.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/h1868/c001.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c001.bin.gz` |
| `nine/fixed/h1868/c002.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/h1868/c003.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c003.bin.gz` |
| `nine/fixed/h1868/c004.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c004.bin.gz` |
| `nine/fixed/h1868/c005.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c005.bin.gz` |
| `nine/fixed/h1868/c006.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c006.bin.gz` |
| `nine/fixed/h1868/c007.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/fixed/h1868/c008.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c008.bin.gz` |
| `nine/fixed/h1868/c009.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c009.bin.gz` |
| `nine/fixed/h1868/threshold_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/threshold_scale.bin.gz` |
| `nine/native_original31/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/native_original31/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/native_original31/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/native_original31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `nine/native_original31/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `nine/native_original31/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine/native_original31/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `nine/native_original31/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `nine/native_original31/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine/native_original31/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `nine/native_original31/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine/native_original31/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `nine/native_original31/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine/native_original31/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `nine/native_original31/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/native_original31/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `nine/native_original31/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `nine/native_original31/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `nine/native_original31/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine/native_original31/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive11/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive11/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive11/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive11/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive11/exact_ring.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/exact_ring.py` |
| `positive11/provenance/70-residue-orientation__eleven__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive11/provenance/compact44_COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive11/provenance/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive11/provenance/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive11/provenance/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `positive11/provenance/source70_weighted_carrier_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `provenance/K215_STATUS_AT_PIN.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `provenance/OBJECT_ZFC_AT_PIN.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/review/upstream/OBJECT_ZFC.md` |
| `verification/integer_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/integer_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/nine_independent_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/nine_independent_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/nine_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/nine_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/pell_saturation_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/pell_saturation_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/positive11_normal.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `verification/positive11_optimized.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |

### `87-direct-centered-round12/` (`ConZFC_Direct_Centered_Round12_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/fixed_base/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |
| `direct_audit/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct_audit/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct_audit/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct_audit/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct_audit/sources/KEndpoint221.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint221.lean` |
| `direct_audit/sources/KLowerSeed.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean` |
| `direct_audit/sources/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `direct_audit/sources/KSeedDirect222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` |
| `direct_audit/sources/KSeedInterface222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean` |
| `direct_audit/sources/KThmK.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` |
| `direct_audit/sources/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `direct_audit/sources/L2Axioms222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Axioms222.lean` |
| `direct_audit/sources/L2Root222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root222.lean` |
| `direct_audit/sources/MRDPCore.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean` |
| `direct_audit/sources/Seed222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Seed222.lean` |
| `direct_audit/sources/ZFModels.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` |
| `inherited/round11/inherited/round10/direct/AFFINE_PRODUCT_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/AFFINE_PRODUCT_CERTIFICATES.md` |
| `inherited/round11/inherited/round10/direct/COMMUTATIVE_CERTIFICATES.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/COMMUTATIVE_CERTIFICATES.md` |
| `inherited/round11/inherited/round10/free_carrier_audit/strengthened_lucas.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/report/lucas.tex` |
| `inherited/round11/inherited/round10/integer_source/24_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/24_report.tex` |
| `inherited/round11/inherited/round10/integer_source/25-hybrid12_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `inherited/round11/inherited/round10/integer_source/26-ratio12_PARITY_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/sources/26-ratio12_PARITY_COEFFICIENT_PROOF.md` |
| `inherited/round11/inherited/round10/integer_source/27-wave4_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `inherited/round11/inherited/round10/integer_source/COMPANIONS_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `inherited/round11/inherited/round10/integer_source/PRIME_PADDING.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_prime_padding.md` |
| `inherited/round11/inherited/round10/integer_source/Q42_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/PROOF.md` |
| `inherited/round11/inherited/round10/integer_source/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `inherited/round11/inherited/round10/integer_source/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `inherited/round11/inherited/round10/norm/final10/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/PROOF.md` |
| `inherited/round11/inherited/round10/packing/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/PROOF.md` |
| `inherited/round11/packing/certified/prior_kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/gapN86_kernels.json` |
| `inherited/round11/packing/certified/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `low_degree/coefficients/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `low_degree/coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `low_degree/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `low_degree/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `low_degree/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `low_degree/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `low_degree/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `low_degree/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `low_degree/coefficients/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `low_degree/coefficients/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `low_degree/coefficients/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `low_degree/inherited/round11_dependencies/34-integer14_coefficients_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `low_degree/inherited/round11_dependencies/34-integer14_coefficients_sources_WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `low_degree/inherited/round11_dependencies/62-sign-and-norm_quartic42_companions_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/62-sign-and-norm/quartic42/companions/PROOF.md` |
| `low_degree/inherited/round11_dependencies/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `low_degree/inherited/round11_dependencies/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `low_degree/inherited/round11_dependencies/ACTIVE_FORMALIZATION_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/baseline/active_research_README.md` |
| `low_degree/inherited/round11_dependencies/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `low_degree/inherited/round11_dependencies/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `low_degree/inherited/round11_dependencies/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `low_degree/inherited/round11_dependencies/ORIENTATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `low_degree/inherited/round11_dependencies/QUARTIC45_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/QUARTIC45_PROOF.md` |
| `low_degree/inherited/round11_dependencies/SEXTIC_PIVOT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/integer34/PROOF_SEXTIC34.md` |
| `low_degree/inherited/round11_dependencies/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `low_degree/inherited/round11_dependencies/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `low_degree/inherited/round11_dependencies/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `low_degree/inherited/round11_dependencies/quartic45.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json` |
| `norm/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `norm/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `norm/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `norm/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `norm/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `norm/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `norm/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `norm/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `norm/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `norm/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `norm/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `norm/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `norm/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `norm/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `norm/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `norm/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `norm/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `norm/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `norm/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `norm/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `norm/provenance/BASELINE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/signed/SOURCE_PINS.json` |
| `norm/provenance/PACKING_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/SOURCE_PINS.json` |
| `norm/provenance/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `norm/provenance/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `norm/provenance/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `norm/provenance/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `norm/provenance/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `positive/interfaces/ORDINARY_KERNEL.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `positive/interfaces/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `positive/interfaces/three_root_norm.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `positive/interfaces/weighted_carrier.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `positive/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/native/FETCH_PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/FETCH_PROVENANCE.json` |
| `positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `source/source_original.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |

### `88-root-fusion13/` (`ConZFC_13_Integer_Norms_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |

### `89-shared-certificates/` (`ConZFC_Shared_Certificates_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coordinate_family/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `coordinate_family/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `coordinate_family/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `coordinate_family/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `coordinate_family/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `coordinate_family/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `coordinate_family/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `coordinate_family/polynomial.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |
| `coordinate_family/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `coordinate_family/upstream/source34/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `coordinate_family/upstream/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coordinate_family/upstream/source34/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `coordinate_family/upstream/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coordinate_family/upstream/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coordinate_family/upstream/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `coordinate_family/upstream/source64/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `coordinate_family/upstream/source64/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `coordinate_family/upstream/source64/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `coordinate_family/upstream/source68/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `coordinate_family/upstream/source70/section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/section.tex` |
| `coordinate_family/upstream/source71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `direct/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/provenance/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/provenance/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/provenance/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/provenance/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/provenance/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `report/build.sh` | `Topology/UnknotRecognition/proposals/06/docs/build.sh` |

### `90-fixed-prime-radicals/` (`ConZFC_FixedPrime_Radicals_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `forms/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `forms/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `forms/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `forms/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `forms/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `forms/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `upstream/DETERMINANT_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/report.tex` |
| `upstream/RATIONAL_PELL_DESCENT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `upstream/SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `upstream/calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `upstream/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `upstream/inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `upstream/inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `upstream/inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `upstream/inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `upstream/inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `upstream/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `upstream/inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `upstream/inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `upstream/inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `upstream/inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `upstream/inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `upstream/inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `upstream/inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `upstream/inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `upstream/inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `upstream/inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `upstream/inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `upstream/inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `upstream/parent_pell_congruences.zip` | `docs/incoming/con_zfc_pell_congruences_2026-10-23.zip (arrival eae4f1952b)` |

### `91-prime-separation13/` (`ConZFC_Prime_Separation_13_Integer_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficient_recipe/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coefficient_recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficient_recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficient_recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `inherited/calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `inherited/calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `inherited/source34_six_port_payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `inherited/source34_six_port_payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `inherited/source34_six_port_payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `inherited/source34_six_port_payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `inherited/source34_six_port_payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `inherited/source34_six_port_payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `inherited/source61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `new_integer_compression/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `new_integer_compression/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `new_integer_compression/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `new_integer_compression/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `new_integer_compression/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `new_integer_compression/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `ten_integer/provenance/calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `ten_integer/provenance/calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `ten_integer/upstream/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `ten_integer/upstream/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `ten_integer/upstream/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `ten_integer/upstream/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `ten_integer/upstream/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `ten_integer/upstream/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `ten_integer/upstream/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `ten_integer/upstream/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `ten_integer/upstream/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `ten_integer/upstream/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `ten_integer/upstream/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `ten_integer/upstream/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `ten_integer/upstream/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `ten_integer/upstream/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `ten_integer/upstream/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `ten_integer/upstream/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `ten_integer/upstream/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `ten_integer/upstream/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `ten_integer/upstream/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `ten_integer/upstream/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `SHA256SUMS.txt` | not staged: checksum ledger |

### `92-parity-norms/` (`con-zfc-parity-norms-2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `provenance/incoming-README.md` | `docs/incoming/README.md` |
| `provenance/source61-congruence-carriers.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `provenance/source67-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/README.md` |
| `upstream/pell-congruences-source/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `upstream/pell-congruences-source/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `upstream/pell-congruences-source/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `upstream/pell-congruences-source/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `upstream/pell-congruences-source/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `upstream/pell-congruences-source/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `upstream/pell-congruences-source/coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/pell-congruences-source/coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `upstream/pell-congruences-source/coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/pell-congruences-source/coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream/pell-congruences-source/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/pell-congruences-source/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `upstream/pell-congruences-source/inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `upstream/pell-congruences-source/inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `upstream/pell-congruences-source/inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/pell-congruences-source/inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `upstream/pell-congruences-source/inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `upstream/pell-congruences-source/inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `upstream/pell-congruences-source/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `upstream/pell-congruences-source/inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `upstream/pell-congruences-source/inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `upstream/pell-congruences-source/inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `upstream/pell-congruences-source/inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `upstream/pell-congruences-source/inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `upstream/pell-congruences-source/inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/pell-congruences-source/inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `upstream/pell-congruences-source/inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `upstream/pell-congruences-source/inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `upstream/pell-congruences-source/inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `upstream/pell-congruences-source/inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `upstream/pell-congruences-source/inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `upstream/pell-congruences-source/inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `upstream/pell-congruences-source/nine_full_radical/circuit_helper.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/59-degree-separated/nine_free_adjunct/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/kernels.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/data/layout.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/layout.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROVENANCE.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive_degree.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_natural_degree.json` |
| `upstream/pell-congruences-source/positive/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `upstream/pell-congruences-source/positive/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `upstream/pell-congruences-source/positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `upstream/pell-congruences-source/positive/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `upstream/pell-congruences-source/positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `upstream/pell-congruences-source/positive/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `upstream/pell-congruences-source/positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `upstream/pell-congruences-source/positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `upstream/pell-congruences-source/positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `upstream/pell-congruences-source/positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `upstream/pell-congruences-source/positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `upstream/pell-congruences-source/positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `upstream/pell-congruences-source/positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `upstream/pell-congruences-source/positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream/pell-congruences-source/positive/native/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `upstream/pell-congruences-source/positive/native/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `upstream/pell-congruences-source/positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `upstream/pell-congruences-source/positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `upstream/pell-congruences-source/positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `upstream/pell-congruences-source/positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `upstream/pell-congruences-source/positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `upstream/pell-congruences-source/positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `upstream/pell-congruences-source/positive/upstream/package52_Y_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `upstream/pell-congruences-source/positive/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `upstream/pell-congruences-source/positive/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `upstream/pell-congruences-source/positive/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `upstream/pell-congruences-source/positive/upstream/source69_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `upstream/pell-congruences-source/positive/upstream/source69_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/report/report.tex` |
| `upstream/pell-congruences-source/positive/upstream/source70_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `upstream/pell-congruences-source/positive/upstream/source70_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/section.tex` |
| `upstream/pell-congruences-source/positive/upstream/source70_weighted_source.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `upstream/pell-congruences-source/positive/upstream/source72_signed_lemma.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/report.tex` |
| `upstream/pell-congruences-source/positive/upstream/source74_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/report.tex` |
| `SHA256SUMS` | not staged: checksum ledger |
| `upstream/pell-congruences-source/SHA256SUMS` | not staged: checksum ledger |

### `93-parity-pell-witnesses/` (`con-zfc-parity-norms-2026-10-23 (2).zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct-quartic/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |
| `direct-quartic/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct-quartic/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct-quartic/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct-quartic/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `integer-norms/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer-norms/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer-norms/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer-norms/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer-norms/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer-norms/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer-norms/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer-norms/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer-norms/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer-norms/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer20/parent/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer20/parent/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer20/parent/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer20/parent/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer20/parent/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer20/parent/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `provenance/k215-calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `provenance/k215-calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `provenance/saturated-parent/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `provenance/saturated-parent/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `provenance/saturated-parent/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `provenance/saturated-parent/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `provenance/saturated-parent/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `provenance/saturated-parent/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `provenance/saturated-parent/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `provenance/saturated-parent/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `provenance/saturated-parent/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `provenance/saturated-parent/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `provenance/saturated-parent/upstream/34-integer14_coefficients_COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `provenance/saturated-parent/upstream/64-structural-reductions_integer41_PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `provenance/saturated-parent/upstream/64-structural-reductions_integer41_PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `provenance/saturated-parent/upstream/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `provenance/saturated-parent/upstream/FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `provenance/saturated-parent/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `provenance/saturated-parent/upstream/ORIENTATION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `provenance/saturated-parent/upstream/RATIONAL_PELL_DESCENT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `provenance/saturated-parent/upstream/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `provenance/saturated-parent/upstream/polynomial_original.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/polynomial.py` |

### `94-direct-projection7617/` (`ConZFC_Direct_Projection_7617.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `provenance/logical/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `provenance/logical/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `provenance/logical/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `provenance/logical/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `provenance/logical/KEndpoint221.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint221.lean` |
| `provenance/logical/KLowerSeed.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean` |
| `provenance/logical/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `provenance/logical/KSeedDirect222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` |
| `provenance/logical/KSeedInterface222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean` |
| `provenance/logical/KThmK.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` |
| `provenance/logical/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `provenance/logical/L2Axioms222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Axioms222.lean` |
| `provenance/logical/L2Root222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root222.lean` |
| `provenance/logical/MRDPCore.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean` |
| `provenance/logical/Seed222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Seed222.lean` |
| `provenance/logical/ZFModels.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` |
| `source/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |

### `95-synchronized-certificates/` (`ConZFC_Synchronized_Certificates_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `build_report.sh` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/161-selectors-build.sh` |
| `provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `report.aux` | not staged: TeX build artifact (`*.aux`) |
| `report.log` | not staged: log file (`*.log`) |
| `report.out` | not staged: TeX build artifact (`*.out`) |

### `96-batched-certificates/` (`con_zfc_batched_certificates_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/upstream/direct/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/upstream/direct/provenance/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/upstream/direct/provenance/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/upstream/direct/provenance/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/upstream/direct/provenance/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/upstream/direct/provenance/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `guard13/upstream/con-zfc-root-fusion-2026-10-24/verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |
| `report/report.aux` | not staged: TeX build artifact (`*.aux`) |
| `report/report.log` | not staged: log file (`*.log`) |
| `report/report.out` | not staged: TeX build artifact (`*.out`) |
| `report/report.toc` | not staged: TeX build artifact (`*.toc`) |

### `97-twelve-interpolation/` (`ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `inherited/root_fusion/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `inherited/root_fusion/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `inherited/root_fusion/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `inherited/root_fusion/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `inherited/root_fusion/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `inherited/root_fusion/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `inherited/root_fusion/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `inherited/root_fusion/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `inherited/root_fusion/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `inherited/root_fusion/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `inherited/root_fusion/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `inherited/root_fusion/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `inherited/root_fusion/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `inherited/root_fusion/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `inherited/root_fusion/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `inherited/root_fusion/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `inherited/root_fusion/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `inherited/root_fusion/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `inherited/root_fusion/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `inherited/root_fusion/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `provenance/signed_guards/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `inherited/root_fusion/verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |
| `report/report.aux` | not staged: TeX build artifact (`*.aux`) |
| `report/report.log` | not staged: log file (`*.log`) |
| `report/report.out` | not staged: TeX build artifact (`*.out`) |
| `report/report.toc` | not staged: TeX build artifact (`*.toc`) |
| `verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |

### `98-congruence-certificates/` (`ConZFC_Congruence_Certificates_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/upstream/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/upstream/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/upstream/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/upstream/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `integer/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer/upstream/fixed_prime/upstream/calibration/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer/upstream/fixed_prime/upstream/calibration/ZFC_INTERNALIZATION_SCOPE.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/63-sign-recovery/reviews/ZFC_INTERNALIZATION_SCOPE.md` |
| `integer/upstream/fixed_prime/upstream/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/fixed_prime/upstream/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `integer/upstream/fixed_prime/upstream/inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer/upstream/fixed_prime/upstream/inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `integer/upstream/fixed_prime/upstream/inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `integer/upstream/fixed_prime/upstream/inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/fixed_prime/upstream/inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/fixed_prime/upstream/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `integer/upstream/fixed_prime/upstream/inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `integer/upstream/fixed_prime/upstream/inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `integer/upstream/fixed_prime/upstream/inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/fixed_prime/upstream/inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer/upstream/fixed_prime/upstream/inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `integer/upstream/root_fusion/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer/upstream/root_fusion/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer/upstream/root_fusion/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer/upstream/root_fusion/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer/upstream/root_fusion/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer/upstream/root_fusion/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `integer/upstream/root_fusion/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `positive/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/coefficients/recipe/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/coefficients/recipe/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/coefficients/recipe/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive/coefficients/recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/coefficients/recipe/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |

### `99-shared-pell608/` (`ConZFC_Shared_Pell_608_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `provenance/inherited/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `provenance/inherited/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `provenance/inherited/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `provenance/inherited/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `provenance/inherited/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |

### `100-quartics407-888/` (`ConZFC_407_888_Quartics_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `upstream/provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `upstream/provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `upstream/provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `upstream/provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `upstream/provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `upstream/provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `SHA256SUMS` | not staged: checksum ledger |

### `101-constructive-reductions/` (`ConZFC_Constructive_Reductions_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `integer14/upstream/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer14/upstream/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer14/upstream/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer14/upstream/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer14/upstream/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer14/upstream/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer14/upstream/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer14/upstream/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer14/upstream/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer14/upstream/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer14/upstream/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer14/upstream/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer14/upstream/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer14/upstream/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer14/upstream/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer14/upstream/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `integer14/upstream/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `integer14/upstream/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `integer14/upstream/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `integer14/upstream/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `integer14/upstream/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer14/upstream/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer14/upstream/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `integer14/upstream/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `integer14/upstream/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `nine/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/circuit.py` |
| `nine/compact/coefficients/compact_tuple/K.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/K.bin.gz` |
| `nine/compact/coefficients/compact_tuple/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MC.bin.gz` |
| `nine/compact/coefficients/compact_tuple/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MF_source.bin.gz` |
| `nine/compact/coefficients/compact_tuple/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/compact/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/K.bin.gz` |
| `nine/compact/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MC.bin.gz` |
| `nine/compact/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MF_source.bin.gz` |
| `nine/compact/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/compact/data/source.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/source.json` |
| `nine/compact/inherited_h2082_kernels.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/kernels.json` |
| `nine/compact/inherited_h2082_layout.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/layout.json` |
| `nine/compact/provenance/SOURCE31_ADAPTER.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/SOURCE31_ADAPTER.md` |
| `nine/compact/provenance/interface_proof.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/interface_proof.md` |
| `nine/compact/provenance/nine-PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/nine-PROOF.md` |
| `nine/compact/provenance/source-GAP_SOURCE_PROOF.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/source-GAP_SOURCE_PROOF.md` |
| `nine/data/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `nine/fixed/boundary/base_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/base_scale.bin.gz` |
| `nine/fixed/boundary/c000.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/boundary/c001.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c001.bin.gz` |
| `nine/fixed/boundary/c002.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/boundary/c003.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c003.bin.gz` |
| `nine/fixed/boundary/c004.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c004.bin.gz` |
| `nine/fixed/boundary/c005.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c005.bin.gz` |
| `nine/fixed/boundary/c006.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c006.bin.gz` |
| `nine/fixed/boundary/c007.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/fixed/boundary/c008.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c008.bin.gz` |
| `nine/fixed/boundary/c009.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c009.bin.gz` |
| `nine/fixed/boundary/threshold_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/threshold_scale.bin.gz` |
| `nine/fixed/compact/base_scale.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/integer/fixed/beta_source.bin.gz` |
| `nine/fixed/compact/c006.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/fixed/compact/c008.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/54-calibrated-carry/integer/fixed/q00b46663e441.bin.gz` |
| `nine/inherited/NineRatio.lean` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/references/NineRatio.lean` |
| `nine/inherited/nine71.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `nine/inherited/nine71_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `nine/inherited/ratio59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/inherited/source65_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `nine/native_original31/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/native_original31/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/native_original31/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/native_original31/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `nine/native_original31/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `nine/native_original31/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `nine/native_original31/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `nine/native_original31/payloads/K.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/K.bin` |
| `nine/native_original31/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine/native_original31/payloads/MC.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MC.bin` |
| `nine/native_original31/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine/native_original31/payloads/MF_source.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/MF_source.bin` |
| `nine/native_original31/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine/native_original31/payloads/beta.bin` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/beta.bin` |
| `nine/native_original31/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/native_original31/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `nine/native_original31/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `nine/native_original31/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `nine/native_original31/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `nine/native_original31/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |

### `102-direct-quartics3776/` (`ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `signed_quotients/source/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `source_calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `source_calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `source_calibration/KEind222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean` |
| `source_calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `source_calibration/KLowerQHyp.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean` |
| `source_calibration/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `source_calibration/KSeedDirect222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` |
| `source_calibration/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `SHA256SUMS` | not staged: checksum ledger |

### `103-shared-pell1873/` (`ConZFC_Shared_Pell_1873.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `provenance/logical/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `provenance/logical/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `provenance/logical/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `provenance/logical/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `provenance/logical/KEndpoint221.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint221.lean` |
| `provenance/logical/KLowerSeed.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean` |
| `provenance/logical/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `provenance/logical/KSeedDirect222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean` |
| `provenance/logical/KSeedInterface222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean` |
| `provenance/logical/KThmK.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` |
| `provenance/logical/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `provenance/logical/L2Axioms222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Axioms222.lean` |
| `provenance/logical/L2Root222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root222.lean` |
| `provenance/logical/MRDPCore.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean` |
| `provenance/logical/Seed222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Seed222.lean` |
| `provenance/logical/ZFModels.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` |
| `source/horn_shared_source.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/horn_shared_source.json` |
| `SHA256SUMS` | not staged: checksum ledger |

### `104-valuation-signed/` (`ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/upstream/synchronized/build_report.sh` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/161-selectors-build.sh` |
| `direct/upstream/synchronized/provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/upstream/synchronized/provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/upstream/synchronized/provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/upstream/synchronized/provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/upstream/synchronized/provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/upstream/synchronized/provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `integer12/inherited/root_fusion/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer12/inherited/root_fusion/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer12/inherited/root_fusion/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer12/inherited/root_fusion/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer12/inherited/root_fusion/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer12/inherited/root_fusion/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer12/inherited/root_fusion/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `integer12/inherited/root_fusion/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `integer12/inherited/root_fusion/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `integer12/inherited/root_fusion/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `integer12/inherited/root_fusion/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `integer12/inherited/root_fusion/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `integer12/provenance/signed_guards/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `supplemental/ordinary98/inherited/ADAPTIVE_CARRIER_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/73-guard-reanchoring/positive/PROOF.md` |
| `supplemental/ordinary98/inherited/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `supplemental/ordinary98/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `supplemental/ordinary98/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `supplemental/ordinary98/native/FETCH_PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/FETCH_PROVENANCE.json` |
| `supplemental/ordinary98/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `supplemental/ordinary98/native/REBUILD_RECEIPT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `supplemental/ordinary98/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `supplemental/ordinary98/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `supplemental/ordinary98/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `supplemental/ordinary98/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `supplemental/ordinary98/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `supplemental/ordinary98/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `supplemental/ordinary98/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `supplemental/ordinary98/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `supplemental/ordinary98/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `supplemental/ordinary98/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `supplemental/ordinary98/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `supplemental/ordinary98/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `supplemental/ordinary98/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `supplemental/ordinary98/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `supplemental/ordinary98/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `supplemental/ordinary98/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `supplemental/ordinary98/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `supplemental/ordinary98/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `supplemental/ordinary98/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `supplemental/ordinary98/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `supplemental/ordinary98/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `supplemental/ordinary98/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `direct/upstream/synchronized/report.aux` | not staged: TeX build artifact (`*.aux`) |
| `direct/upstream/synchronized/report.log` | not staged: log file (`*.log`) |
| `direct/upstream/synchronized/report.out` | not staged: TeX build artifact (`*.out`) |
| `integer12/inherited/root_fusion/verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |
| `verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |

### `105-bootstrap-certificates/` (`ConZFC_Bootstrap_Certificates_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/equations/parent781/index_shift_certificate.json` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake212-catalogue/diagnostics.json` |
| `direct/equations/parent782/index_shift_certificate.json` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake212-catalogue/diagnostics.json` |
| `direct/equations/parent783/index_shift_certificate.json` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake212-catalogue/diagnostics.json` |
| `direct/provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `nine/fixed/h1868/base_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/base_scale.bin.gz` |
| `nine/fixed/h1868/c000.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/h1868/c001.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c001.bin.gz` |
| `nine/fixed/h1868/c002.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c000.bin.gz` |
| `nine/fixed/h1868/c003.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c003.bin.gz` |
| `nine/fixed/h1868/c004.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c004.bin.gz` |
| `nine/fixed/h1868/c005.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c005.bin.gz` |
| `nine/fixed/h1868/c006.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c006.bin.gz` |
| `nine/fixed/h1868/c007.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/fixed/h1868/c008.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c008.bin.gz` |
| `nine/fixed/h1868/c009.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/c009.bin.gz` |
| `nine/fixed/h1868/threshold_scale.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/fixed/h1868/threshold_scale.bin.gz` |
| `nine/inherited/gap-source-proof.md` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/provenance/source-GAP_SOURCE_PROOF.md` |
| `nine/inherited/original31-binding.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `nine/inherited/original31-coefficient-proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `nine/inherited/ratio-proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `nine/inherited/source65-proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `nine/ports/compact2082/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/K.bin.gz` |
| `nine/ports/compact2082/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MC.bin.gz` |
| `nine/ports/compact2082/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/MF_source.bin.gz` |
| `nine/ports/compact2082/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/coefficients/compact_tuple/beta.bin.gz` |
| `nine/ports/h1868/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `nine/ports/h1868/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `nine/ports/h1868/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `nine/ports/h1868/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `nine/source/compact2082/kernels.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/kernels.json` |
| `nine/source/compact2082/layout.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/layout.json` |
| `nine/source/compact2082/source.json` | `Computability/DiophantineConsistency/candidates/gap2082-compact54/data/H2082/source.json` |
| `nine/source/h1868/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `norms/upstream/positive11/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `norms/upstream/positive11/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `norms/upstream/positive11/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `norms/upstream/positive11/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `norms/upstream/positive11/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `norms/upstream/positive11/native_recipe/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `norms/upstream/positive11/native_recipe/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `norms/upstream/positive11/native_recipe/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `norms/upstream/positive11/native_recipe/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `norms/upstream/positive11/upstream/44-b4-sparse__native__COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `norms/upstream/positive11/upstream/61-congruence-carriers__positive__SIGNED_INDEX_LEMMA.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` |
| `norms/upstream/positive11/upstream/69-cones-pell__positive__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `norms/upstream/positive11/upstream/70-residue-orientation__eleven__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `norms/upstream/positive11/upstream/70-residue-orientation__eleven__build.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/build.py` |
| `norms/upstream/positive11/upstream/70-residue-orientation__eleven__independent_audit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/independent_audit.py` |
| `norms/upstream/positive11/upstream/70-residue-orientation__eleven__p11_positive_degree325.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/p11_positive_degree325.json` |
| `norms/upstream/positive11/upstream/70-residue-orientation__positive__section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `norms/upstream/rootfusion/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `norms/upstream/rootfusion/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `norms/upstream/rootfusion/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `norms/upstream/rootfusion/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `norms/upstream/rootfusion/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `norms/upstream/rootfusion/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `norms/upstream/rootfusion/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `norms/upstream/rootfusion/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `norms/upstream/rootfusion/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `norms/upstream/rootfusion/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |

### `106-compact-certificates-round13/` (`ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct/sources/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct/sources/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `norm/FIXED_COEFFICIENTS.json` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/FIXED_COEFFICIENTS.json` |
| `norm/circuit.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `norm/data/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `norm/data/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `norm/data/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `norm/data/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `norm/data/coefficients_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/data/coefficients_binding.json` |
| `norm/data/source.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/source.json` |
| `norm/fixed/c000.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c000.signed-le.gz` |
| `norm/fixed/c001.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c001.signed-le.gz` |
| `norm/fixed/c002.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c002.signed-le.gz` |
| `norm/fixed/c003.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c003.signed-le.gz` |
| `norm/fixed/c004.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c004.signed-le.gz` |
| `norm/fixed/c005.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c005.signed-le.gz` |
| `norm/fixed/c006.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c006.signed-le.gz` |
| `norm/fixed/c007.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c007.signed-le.gz` |
| `norm/fixed/c008.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c008.signed-le.gz` |
| `norm/fixed/c009.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/c009.signed-le.gz` |
| `norm/fixed/radix.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/radix.signed-le.gz` |
| `norm/fixed/threshold.signed-le.gz` | `Computability/DiophantineConsistency/candidates/norm-tail-sharing/source10/fixed/threshold.signed-le.gz` |
| `norm/provenance/BASELINE_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/signed/SOURCE_PINS.json` |
| `norm/provenance/PACKING_SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/packing/SOURCE_PINS.json` |
| `norm/provenance/upstream/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `norm/provenance/upstream/CONGRUENCE_NORMS_TEN_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/55-congruence-norms/ten/PROOF.md` |
| `norm/provenance/upstream/DEGREE_SEPARATED_SOURCE.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/sun/section.tex` |
| `norm/provenance/upstream/QUARTIC31_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/nine/QUARTIC31_PROOF.md` |
| `norm/provenance/upstream/SIGNED10_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/signed10/SIGNED10_PROOF.md` |
| `radicals/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `radicals/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `radicals/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `radicals/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `radicals/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `radicals/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `radicals/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `radicals/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `radicals/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `radicals/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `radicals/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `radicals/inherited/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `radicals/inherited/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `radicals/inherited/pell_congruences/inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `radicals/inherited/pell_congruences/inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `radicals/inherited/pell_congruences/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `radicals/inherited/pell_congruences/inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `radicals/inherited/pell_congruences/inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `radicals/inherited/pell_congruences/inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `radicals/inherited/pell_congruences/inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `radicals/inherited/pell_congruences/inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `radicals/inherited/pell_congruences/inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `radicals/inherited/pell_congruences/inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `radicals/inherited/pell_congruences/inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `radicals/inherited/pell_congruences/inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `radicals/inherited/pell_congruences/inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `radicals/inherited/pell_congruences/inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `radicals/inherited/pell_congruences/inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `radicals/inherited/pell_congruences/inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `radicals/inherited/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `radicals/inherited/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `radicals/inherited/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `radicals/inherited/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `radicals/inherited/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `radicals/inherited/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `radicals/inherited/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `radicals/inherited/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `radicals/inherited/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `radicals12/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `radicals12/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `radicals12/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `radicals12/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `radicals12/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `radicals12/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `radicals12/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `radicals12/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `radicals12/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `radicals12/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `radicals12/inherited/root_fusion_provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `radicals12/inherited/root_fusion_provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `radicals12/inherited/root_fusion_provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `radicals12/inherited/root_fusion_provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `radicals12/inherited/root_fusion_provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `radicals12/inherited/signed_guards/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `late_direct_audit/FINAL_REPLAY.log` | not staged: log file (`*.log`) |

### `107-dyadic-pell/` (`ConZFC_Dyadic_Pell_Reductions_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct780/upstream/ConZFC_407_888_Quartics_2026-10-24.zip` | `docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip (arrival 3635835b1e)` |
| `dyadic10/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `dyadic10/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `dyadic10/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `dyadic10/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `provenance/calibration61.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `provenance/calibration61_README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/README.md` |
| `provenance/compact44_native_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `direct780/SHA256SUMS.json` | not staged: checksum ledger |

### `108-pell-residues/` (`ConZFC_Pell_Residues_2026-10-23.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `inputs/ConZFC_407_888_Quartics_2026-10-24.zip` | `docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip (arrival 3635835b1e)` |
| `supplemental/integer12/inherited/root_fusion/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `supplemental/integer12/inherited/root_fusion/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `supplemental/integer12/inherited/root_fusion/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `supplemental/integer12/inherited/root_fusion/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `supplemental/integer12/inherited/root_fusion/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `supplemental/integer12/inherited/root_fusion/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `supplemental/integer12/provenance/signed_guards/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `SHA256SUMS` | not staged: checksum ledger |
| `supplemental/integer12/inherited/root_fusion/verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |

### `109-valuations-centered/` (`ConZFC_Valuations_and_Centered_Certificates.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/affine_shared_step.json` | `Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/source/affine_shared_step.json` |
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/inherited_onestack_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/66-gap-congruence/direct/section.tex` |
| `integer12/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `integer12/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `integer12/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `integer12/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `integer12/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `integer12/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `integer12/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `integer12/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `integer12/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `integer12/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `integer12/source_interpolation.zip` | `docs/incoming/ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip (arrival 85ae407001)` |
| `positive10/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive10/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive10/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive10/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive10/provenance/INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive10/provenance/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive10/provenance/SOURCE58_REPORT.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex` |
| `positive10/provenance/compact44/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive10/provenance/compact44/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `positive10/provenance/compact44/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive10/provenance/compact44/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `positive10/provenance/compact44/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `positive10/provenance/compact44/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `positive10/provenance/compact44/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive10/provenance/compact44/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive10/provenance/compact44/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive10/provenance/compact44/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive10/provenance/compact44/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive10/provenance/compact44/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive10/provenance/compact44/native_report.pdf` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.pdf` |
| `positive10/provenance/compact44/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `positive10/provenance/compact44/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `positive10/provenance/compact44/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `positive10/provenance/compact44/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `positive10/provenance/compact44/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `positive10/provenance/compact44/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `positive10/provenance/compact44/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `positive10/provenance/compact44/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `positive10/provenance/compact44/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `positive10/provenance/compact44/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `positive10/provenance/compact44/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `positive10/provenance/compact44/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `positive10/provenance/compact44/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive10/provenance/compact44/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `positive10/provenance/compact44/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive10/provenance/compact44/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `positive10/provenance/source61/congruence_carriers.pdf` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.pdf` |
| `positive10/provenance/source61/congruence_carriers.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `direct_quartic/ConZFC_407_888_Quartics/SHA256SUMS` | not staged: checksum ledger |

### `110-budget-interpolation/` (`ZFC_Diophantine_Budget_Interpolation_2026-10-24.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `baseline/ConZFC_13_Integer_Norms_2026-10-24.zip` | `docs/incoming/ConZFC_13_Integer_Norms_2026-10-24.zip (arrival 751bc067e2)` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `baseline/README.md` | `docs/incoming/README.md` |
| `baseline/con-zfc-parity-norms-2026-10-23.zip` | `docs/incoming/con-zfc-parity-norms-2026-10-23.zip (arrival f6b6c83b1c)` |
| `baseline/replay/results/parity_normal/release.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/audit.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/audit_compact_kernel.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/audit_norm_family.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/audit_shift.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/driver_policy.stdout.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/independent_checks.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/independent_compact_audit.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/parity_optimized/independent_graph_audit.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/rootfusion_normal/release.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `baseline/replay/results/rootfusion_optimized/release.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `eleven/provenance/centered17/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `eleven/provenance/centered17/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `eleven/provenance/centered17/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `eleven/provenance/centered17/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `eleven/provenance/centered17/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `eleven/provenance/centered17/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `eleven/provenance/centered17/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `eleven/provenance/centered17/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `eleven/provenance/centered17/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `eleven/provenance/centered17/upstream/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `eleven/provenance/centered17/upstream/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `eleven/provenance/centered17/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `eleven/provenance/centered18/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `eleven/provenance/centered18/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `eleven/provenance/centered18/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `eleven/provenance/centered18/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `eleven/provenance/centered18/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `eleven/provenance/centered18/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `eleven/provenance/centered18/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `eleven/provenance/centered18/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `eleven/provenance/centered18/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `eleven/provenance/rootfusion/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `eleven/provenance/rootfusion/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `eleven/provenance/rootfusion/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `eleven/provenance/rootfusion/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `eleven/provenance/rootfusion/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `eleven/provenance/rootfusion/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `eleven/provenance/rootfusion/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `eleven/provenance/rootfusion/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `eleven/provenance/rootfusion/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `eleven/provenance/rootfusion/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/provenance/incoming-README.md` | `docs/incoming/README.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/provenance/source61-congruence-carriers.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/provenance/source67-README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/67-oriented-guards/README.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/payloads/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/source34/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/source34/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/source34/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/source34/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PAIR_GUARD_PROOF68.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PAYLOAD_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/SIGNED_DOMAIN_29.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COMPACT_LAYOUT.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/WANG943_LANGUAGE_AND_COMPILER.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/33-signed16/upstream/compiler/WANG943_COEFFICIENTS.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/determinant71/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/determinant71/NEW_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/coefficients/NEW_BINDING.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/determinant71/quartic38.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/integer_forms/quartic38.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/SOURCE_PINS.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/octic29.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/octic29.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/quartic40.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/quartic40_direct.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/quartic40_direct.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/orientation70/sextic34.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/sextic34.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/quartic41.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/circuit_helper.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/norm/final10/circuit.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/BUILD_RECEIPT.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/COEFFICIENT_BINDING.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/README.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/SOURCE_PINS.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/build_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/coefficient_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sections/coefficients.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/K.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/K.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MC.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/saturated-h1868-d/source/data/MF_source.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/payloads/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/24-coefficients.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/24-coefficients.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/25-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/32-integer15/compiler/upstream/mixed125_adapter.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/coefficients/upstream/27-COEFFICIENT_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/upstream/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/59-degree-separated/nine_free_adjunct/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/nine/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/data/kernels.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/kernels.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/65-shared-taps/nine/data/layout.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/sun/data/layout.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/PROVENANCE.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/PROVENANCE.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_positive.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/generated/composed9_positive_degree.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/nine_positive/generated/composed9_natural_degree.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/independent_ring.py` | `Computability/DiophantineConsistency/candidates/positive11-adaptive-shears/independent_ring.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/ACTIVE_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/native/ACTIVE_BINDING.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/COEFFICIENT_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/INDEPENDENT_AUDIT.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/INDEPENDENT_AUDIT.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/README.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/README.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/SOURCE_PINS.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/SOURCE_PINS.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/audit_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/audit_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/native_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_report.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/native_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/native_section.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/product67.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/retained16_system59.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/baseline__product67.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/baseline__retained16_system59.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/baseline/retained16_system59.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__build_coefficients.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/build_coefficients.py` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__k215_transitions.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/k215_transitions.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COEFFICIENTS.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/37-wave5/coefficients/WANG943_COMPACT_LAYOUT.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/coefficients__wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_P67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/FIXED_BLANK_67_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_PELL_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/source/proofs__INHERITED_RETAINED59_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/package52_Y_ABSORPTION_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/package61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/package65_proof.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/65-shared-taps/pell/proof.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source69_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source69_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/report/report.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source70_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/PROOF.md` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source70_section.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/section.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source70_weighted_source.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/positive/section.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source72_signed_lemma.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/72-congruence-sextic/report.tex` |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/upstream/source74_report.tex` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/report.tex` |
| `guard/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `guard/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `guard/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `guard/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `guard/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `guard/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `guard/coefficients/recipe/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `guard/coefficients/recipe/source34_binding.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/BUILD_CHECKS.json` |
| `guard/coefficients/recipe/source34_builder.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/build_coefficients.py` |
| `guard/coefficients/recipe/wang943_tiles.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/coefficients/wang943_tiles.json` |
| `guard/provenance/centered17/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `guard/provenance/centered17/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `guard/provenance/centered17/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `guard/provenance/centered17/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `guard/provenance/centered17/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `guard/provenance/centered17/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `guard/provenance/centered17/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `guard/provenance/centered17/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `guard/provenance/centered17/upstream/ODD_SCALE_27_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ODD_SCALE_27_PROOF.md` |
| `guard/provenance/centered17/upstream/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `guard/provenance/centered17/upstream/RESIDUE_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/integer/PROOF.md` |
| `guard/provenance/centered17/upstream/package61_report.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `guard/provenance/centered18/coefficients/K0.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/K0.bin.gz` |
| `guard/provenance/centered18/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MC.bin.gz` |
| `guard/provenance/centered18/coefficients/MF.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/MF.bin.gz` |
| `guard/provenance/centered18/coefficients/WC.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/WC.bin.gz` |
| `guard/provenance/centered18/coefficients/Walpha.bin.gz` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/integer/coefficients/Walpha.bin.gz` |
| `guard/provenance/centered18/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/beta.bin.gz` |
| `guard/provenance/centered18/coefficients/cone_A.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_A.bin.gz` |
| `guard/provenance/centered18/coefficients/cone_B.bin.gz` | `Computability/DiophantineConsistency/candidates/joint22-centered/coefficients/cone_B.bin.gz` |
| `guard/provenance/centered18/upstream/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `guard/provenance/rootfusion/COEFFICIENT_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `guard/provenance/rootfusion/DETERMINANT_GUARD.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/71-determinant-guards/proofs/DETERMINANT_GUARD.md` |
| `guard/provenance/rootfusion/PAIR_GUARD_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/integer_system/PAIR_GUARD_PROOF.md` |
| `guard/provenance/rootfusion/PROOF41.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF41.md` |
| `guard/provenance/rootfusion/PROOF44.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/PROOF44.md` |
| `guard/provenance/rootfusion/SIGNED_BOOTSTRAP.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/guards/PROOF.md` |
| `guard/provenance/rootfusion/upstream_ordinary/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `guard/provenance/rootfusion/upstream_ordinary/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `guard/provenance/rootfusion/upstream_ordinary/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `guard/provenance/rootfusion/upstream_ordinary/dominated_calculus.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` |
| `guard/provenance/rootfusion/upstream_ordinary/fixed_blank67.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `guard/provenance/rootfusion/upstream_ordinary/k215_ordinary.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `guard/provenance/rootfusion/upstream_ordinary/ordinary36.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `guard/provenance/rootfusion/upstream_ordinary/source25_ordinary_blank.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `guard/provenance/rootfusion/upstream_ordinary/source34_coefficients.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md` |
| `positive/ten_centered/coefficients/K.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/K.bin.gz` |
| `positive/ten_centered/coefficients/MC.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MC.bin.gz` |
| `positive/ten_centered/coefficients/MF_source.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/MF_source.bin.gz` |
| `positive/ten_centered/coefficients/beta.bin.gz` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/coefficients/beta.bin.gz` |
| `positive/ten_centered/generated/normal_build.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/normal_degree_specialization.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/normal_independent_check.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/normal_rebuild_coefficients.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/optimized_build.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/optimized_degree_specialization.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/optimized_independent_check.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/generated/optimized_rebuild_coefficients.py.stderr.txt` | `Logic/FirstOrder/compactness-check/source.log` |
| `positive/ten_centered/upstream/interfaces/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `positive/ten_centered/upstream/interfaces/K215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `positive/ten_centered/upstream/interfaces/ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md` |
| `positive/ten_centered/upstream/interfaces/PELL_LEMMA_AUDIT.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/sources/PELL_LEMMA_AUDIT.md` |
| `positive/ten_centered/upstream/interfaces/compact44_BINDING.json` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json` |
| `positive/ten_centered/upstream/interfaces/compact44_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md` |
| `positive/ten_centered/upstream/interfaces/compact44_recipe.py` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/build_coefficients.py` |
| `positive/ten_centered/upstream/interfaces/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `positive/ten_centered/upstream/interfaces/kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `positive/ten_centered/upstream/interfaces/normalized_source61.tex` | `Computability/DiophantineConsistency/candidates/ten-positive-free-j/source/SOURCE61.tex` |
| `positive/ten_centered/upstream/interfaces/source36_BLANK_HELICAL_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/BLANK_HELICAL_PROOF.md` |
| `positive/ten_centered/upstream/interfaces/source36_FIXED_BLANK_67_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/FIXED_BLANK_67_PROOF.md` |
| `positive/ten_centered/upstream/interfaces/source36_ORDINARY_BLANK_PROOF.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/ORDINARY_BLANK_PROOF.md` |
| `positive/ten_centered/upstream/interfaces/source61_PROOF13.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF13.md` |
| `positive/ten_centered/upstream/interfaces/source61_PROOF14.md` | `Computability/DiophantineConsistency/con-zfc-diophantine-forms/61-congruence-carriers/positive/PROOF14.md` |
| `provenance/certificate_predecessor/upstream/K215_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `provenance/certificate_predecessor/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `report/qa/bounds.json` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/67-under246-research-agent_state-symbolic_merge_survivors.json` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/verification/LATEX_BUILD.log` | not staged: log file (`*.log`) |
| `baseline/replay/tex_check/build.log` | not staged: log file (`*.log`) |
| `eleven/check_normal.log` | not staged: log file (`*.log`) |
| `eleven/check_optimized.log` | not staged: log file (`*.log`) |
| `eleven/degree.log` | not staged: log file (`*.log`) |
| `eleven/degree_optimized.log` | not staged: log file (`*.log`) |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/SHA256SUMS` | not staged: checksum ledger |
| `finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/SHA256SUMS` | not staged: checksum ledger |
| `guard/check_normal.log` | not staged: log file (`*.log`) |
| `guard/check_optimized.log` | not staged: log file (`*.log`) |
| `positive/ten_centered/audit.log` | not staged: log file (`*.log`) |
| `positive/ten_centered/degree.log` | not staged: log file (`*.log`) |
| `review/budget/normal.log` | not staged: log file (`*.log`) |
| `review/budget/optimized.log` | not staged: log file (`*.log`) |
| `review/eleven/normal.log` | not staged: log file (`*.log`) |
| `review/eleven/optimized.log` | not staged: log file (`*.log`) |
| `review/positive/normal.log` | not staged: log file (`*.log`) |
| `review/positive/optimized.log` | not staged: log file (`*.log`) |

### `ZFC_Diophantine_Centered_Compression_2026-10-24_Dependency.zip` (duplicate archive, no directory)

| Delivered member | Same bytes in the repository |
|---|---|
| `ZFC_Diophantine_Centered_Compression/incoming/ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | `docs/incoming/ZFC_Diophantine_Joint_Guards_2026-10-24.zip (arrival c1a102936a)` |
