# Placement record: batch 218 (wave 2)

Intake record, not a delivered file. The seven archives of the arrival
commit `7be2780f26` ("Con(ZFC) in Diophantine form (wave-2)") were extracted
straight from the committed ZIPs into numbered directories 09–15, with the
single wrapper directory removed (archive 11 has none). Nothing was edited
and nothing was run at intake.

**Wave 1 is superseded.** By Vladimir's direction the wave-2 packages
completely supersede the eight batch-217 packages, so directories `01-…` to
`08-…` were removed from the tree in the same commit. They remain
recoverable from placement `084e120830` (or any commit up to the one before
this placement), whose own `PLACEMENT.md` maps their omitted members; their
archives remain in arrival `2fd49a1a9d`.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent *outside this report* is omitted; the
  tables below name the shortest repository path holding the same bytes.
  Wave-2 copies of wave-1 files are therefore kept, since wave 1 leaves the
  tree. Licence and notice files are always kept. All seven packages pin
  `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

The delivered verification drivers read their vendored copies at the
delivered paths. To rerun a package, extract its archive from the arrival
commit into a scratch directory and run it there:

```sh
git show 7be2780f26:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `09-combined13/` | `con-zfc-combined-reductions.zip` | 86 | 77 | 8 | 1 | `con-zfc-combined-reductions/` |
| `10-synthesis14/` | `con-zfc-diophantine-synthesis-2026-10-22.zip` | 69 | 53 | 16 | 0 | `con-zfc-diophantine-synthesis/` |
| `11-t4/` | `ZFC_Diophantine_Combined_T4_2026-10-22.zip` | 118 | 111 | 5 | 2 | none |
| `12-gap-norm14/` | `ProveIt_ConZFC_Diophantine_Synthesis_2026-10-22.zip` | 87 | 66 | 13 | 8 | `zfc_diophantine_synthesis/` |
| `13-four-cell14/` | `ConZFC_Synthesis_14vars_2026-10-22.zip` | 64 | 48 | 16 | 0 | `con_zfc_synthesis/` |
| `14-integer29/` | `con_zfc_synthesis_2026-10-22.zip` | 75 | 45 | 29 | 1 | `con_zfc_synthesis_2026-10-22/` |
| `15-release/` | `combined_con_zfc_3b201cd.zip` | 141 | 135 | 6 | 0 | `combined_con_zfc/` |

Total: 640 members.

## `09-combined13/` (`con-zfc-combined-reductions.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/compiler/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `upstream/compiler/FIXED_RAW_UNIVERSAL_77_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` |
| `upstream/compiler/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `upstream/compiler/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/compiler/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/compiler/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `upstream/compiler/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `SHA256SUMS` | not staged: checksum ledger |

## `10-synthesis14/` (`con-zfc-diophantine-synthesis-2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `evidence/k215_verification_readme.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `evidence/lean/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `evidence/lean/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `evidence/lean/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `evidence/licenses/ProveIt_LICENSE` | `LICENSE` |
| `evidence/proofs/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `evidence/proofs/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `evidence/proofs/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `evidence/proofs/complete84_signed_quotient_absorption.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_absorption.md` |
| `evidence/proofs/complete84_signed_quotient_soundness_scout.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_soundness_scout.md` |
| `evidence/proofs/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `evidence/proofs/complete90_signed_root_elimination.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete90_signed_root_elimination.md` |
| `evidence/proofs/review_complete84_signed_quotient_soundness.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_signed_quotient_soundness.md` |
| `machine/KDense215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` |
| `machine/Table215.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table215.v` |
| `machine/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |

## `11-t4/` (`ZFC_Diophantine_Combined_T4_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `bridge/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `bridge/sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `bridge/sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `bridge/sources/ordinary_k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `comparison/sources/PELL_RELAXED_AUXILIARY_PROOF.md` | `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/07-native-fiber-source-PELL_RELAXED_AUXILIARY_PROOF.md` |
| `SHA256SUMS.json` | not staged: checksum ledger |
| `bridge/SHA256SUMS.json` | not staged: checksum ledger |

## `12-gap-norm14/` (`ProveIt_ConZFC_Diophantine_Synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `upstream/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `upstream/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `upstream/K215_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/NOTICE.md` |
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `upstream/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `upstream/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `upstream/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `upstream/k215_verification_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `SHA256SUMS.txt` | not staged: checksum ledger |
| `verification/01.log` | not staged: log file (`*.log`) |
| `verification/02.log` | not staged: log file (`*.log`) |
| `verification/03.log` | not staged: log file (`*.log`) |
| `verification/04.log` | not staged: log file (`*.log`) |
| `verification/05.log` | not staged: log file (`*.log`) |
| `verification/06.log` | not staged: log file (`*.log`) |
| `verification/07.log` | not staged: log file (`*.log`) |

## `13-four-cell14/` (`ConZFC_Synthesis_14vars_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `references/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `references/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `references/1980/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `references/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `references/calibration/K215_ordinary_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `references/calibration/K215_verification_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `references/calibration/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `references/native/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `references/native/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `references/native/complete84_signed_quotient_absorption.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_absorption.md` |
| `references/native/complete84_signed_quotient_soundness_scout.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_soundness_scout.md` |
| `references/native/complete90_signed_root_elimination.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete90_signed_root_elimination.md` |
| `references/native/complete92_norm_unit_guard.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete92_norm_unit_guard.md` |
| `references/native/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `references/native/review_complete84_signed_quotient_soundness.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_signed_quotient_soundness.md` |
| `vendor/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |

## `14-integer29/` (`con_zfc_synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `data/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `dependencies/BASE_TWO_PELL_89_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/BASE_TWO_PELL_89_PROOF.md` |
| `dependencies/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` |
| `dependencies/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `dependencies/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md` |
| `dependencies/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `dependencies/EXPLORATION_FIXED_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` |
| `dependencies/EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `dependencies/EXPLORATION_MARKED_PERIODIC_TM_PADDING.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_MARKED_PERIODIC_TM_PADDING.md` |
| `dependencies/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_77_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_80_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_80_PROOF.md` |
| `dependencies/FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `dependencies/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `dependencies/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `dependencies/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `dependencies/complete74_factored_first_norm.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.md` |
| `dependencies/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `dependencies/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `dependencies/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `dependencies/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `dependencies/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `dependencies/k215_ordinary_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `dependencies/k215_verification_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `dependencies/pell_fixed_affine_exponent52.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` |
| `dependencies/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `SHA256SUMS` | not staged: checksum ledger |

## `15-release/` (`combined_con_zfc_3b201cd.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `evidence/diophantine_zfc_compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_half_binomial.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial.json` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
