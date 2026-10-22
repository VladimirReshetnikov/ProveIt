# Placement record: batch 217

Intake record, not a delivered file. The eight archives of the arrival commit
`2fd49a1a9d` ("Con(ZFC) in Diophantine form") were extracted straight from
the committed ZIPs into one numbered directory each, with the single wrapper
directory removed (archive 01 has none). Nothing was edited and nothing was
run at intake.

Two classes of member are not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent is omitted; the table below names one
  repository path holding the same bytes. Licence and notice files are kept
  even when identical, beside the package they govern. All eight packages
  pin `cdd582bec13f908df3711fa9e05d1ddac368a5db`, and every omitted copy is
  also present at `HEAD`.
- **Checksum ledgers.** `SHA256SUMS` and `SHA256SUMS.*` are excluded by the
  root `.gitignore` (repository policy); they were not verified.

The delivered verification drivers read their vendored copies at the
delivered paths. To rerun a package, extract its archive from the arrival
commit into a scratch directory and run it there:

```sh
git show 2fd49a1a9d:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored ledgers | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `01-explicit82/` | `ZFC_Diophantine_Explicit_82_2026-10-22.zip` | 39 | 36 | 2 | 1 | none |
| `02-system63/` | `zfc_diophantine.zip` | 82 | 65 | 16 | 1 | `zfc_diophantine/` |
| `03-system64/` | `zfc-diophantine.zip` | 123 | 29 | 93 | 1 | `zfc-diophantine/` |
| `04-poly73/` | `zfc_diophantine (1).zip` | 44 | 31 | 12 | 1 | `zfc_diophantine/` |
| `05-fixed15-16/` | `ZFC_Diophantine_15_16_2026-10-22.zip` | 75 | 46 | 29 | 0 | `zfc_diophantine_20261022/` |
| `06-blank67/` | `zfc_diophantine_67.zip` | 69 | 34 | 34 | 1 | `zfc_diophantine_67/` |
| `07-fixed70/` | `zfc_diophantine_fixed70.zip` | 56 | 41 | 14 | 1 | `zfc_diophantine/` |
| `08-start-only67/` | `diophantine_zfc_cdd582b.zip` | 112 | 47 | 64 | 1 | `diophantine_zfc/` |

Total: 600 members.

## `01-explicit82/` (`ZFC_Diophantine_Explicit_82_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `native/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `tag/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `SHA256SUMS.json` | not staged: checksum ledger (`.gitignore`) |

## `02-system63/` (`zfc_diophantine.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `ASYMMETRIC_SCALE.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `RAW75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `UPSTREAM_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/NOTICE.md` |
| `complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `complete84_scaled_strong_output.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream_licenses/candidate-k215/licenses/SOURCE_PINS.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/SOURCE_PINS.json` |
| `upstream_licenses/candidate-k215/provenance.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/provenance.json` |
| `upstream_licenses/candidate-k215/provenance/partial-selector/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/ATTRIBUTION.md` |
| `upstream_licenses/candidate-k215/provenance/partial-selector/provenance/k217-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/NOTICE.md` |
| `upstream_licenses/candidate-k215/provenance/partial-selector/provenance/parent-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `upstream_licenses/candidate-k215/provenance/permuted-commands/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/ATTRIBUTION.md` |
| `upstream_licenses/candidate-k215/provenance/permuted-commands/provenance/K218_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/parent-NOTICE.md` |
| `upstream_licenses/candidate-k215/provenance/permuted-commands/provenance/PREDECESSOR_ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |

## `03-system64/` (`zfc-diophantine.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `source/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `vendor/BASE_TWO_PELL_89_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/BASE_TWO_PELL_89_PROOF.md` |
| `vendor/CorrectDense215.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v` |
| `vendor/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` |
| `vendor/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `vendor/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md` |
| `vendor/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `vendor/EXPLORATION_FIXED_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` |
| `vendor/EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `vendor/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` |
| `vendor/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` |
| `vendor/EXPLORATION_THREE_CELL_PERIOD_LIFT.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_THREE_CELL_PERIOD_LIFT.md` |
| `vendor/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_77_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_80_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_80_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_82_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_82_PROOF.md` |
| `vendor/FIXED_RAW_UNIVERSAL_84_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_84_PROOF.md` |
| `vendor/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `vendor/K215-K218_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/parent-NOTICE.md` |
| `vendor/K215-PREDECESSOR_ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `vendor/K215-candidate-README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `vendor/K215-k217-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/NOTICE.md` |
| `vendor/K215-licenses-LICENSE.ProveIt` | `LICENSE` |
| `vendor/K215-licenses-LICENSE.Wade` | `lib/jeff-busy-beaver-zfc254/ZF/generator/LICENSE.wade` |
| `vendor/K215-licenses-NOTICE-normalized-source.txt` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/NOTICE-normalized-source.txt` |
| `vendor/K215-licenses-NOTICE-original245.txt` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/NOTICE-original245.txt` |
| `vendor/K215-licenses-SOURCE_PINS.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/SOURCE_PINS.json` |
| `vendor/K215-ordinary-proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `vendor/K215-parent-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `vendor/K215-partial-selector-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/ATTRIBUTION.md` |
| `vendor/K215-partial-selector-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/NOTICE.md` |
| `vendor/K215-permuted-commands-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/ATTRIBUTION.md` |
| `vendor/K215-verification-README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `vendor/K215_NOTICE.txt` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/NOTICE.md` |
| `vendor/KBoot215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KBoot215.lean` |
| `vendor/KDense215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` |
| `vendor/KDenseBridge.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDenseBridge.lean` |
| `vendor/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `vendor/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `vendor/KSites215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSites215.lean` |
| `vendor/KSource215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean` |
| `vendor/KTable215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean` |
| `vendor/PELL_COMMON_WITNESS_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_COMMON_WITNESS_PROOF.md` |
| `vendor/PELL_DOUBLED_INDEX_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_DOUBLED_INDEX_PROOF.md` |
| `vendor/PELL_GAP_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_GAP_PROOF.md` |
| `vendor/PELL_ODD_ROOT_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_ODD_ROOT_PROOF.md` |
| `vendor/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `vendor/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `vendor/ProveIt-LICENSE.txt` | `LICENSE` |
| `vendor/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `vendor/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `vendor/complete75_gamma_dominance_elimination102.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_gamma_dominance_elimination102.md` |
| `vendor/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `vendor/complete75_half_binomial_compiler.py` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py` |
| `vendor/complete75_norm_product89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product89.md` |
| `vendor/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `vendor/complete75_positive_elimination.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_elimination.md` |
| `vendor/complete75_positive_root89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_root89.md` |
| `vendor/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `vendor/complete75_strong_reduction89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_strong_reduction89.md` |
| `vendor/complete84_scaled_strong_output.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `vendor/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `vendor/complete84_signed_quotient_absorption.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_absorption.md` |
| `vendor/complete84_signed_quotient_soundness_scout.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_soundness_scout.json` |
| `vendor/complete84_signed_quotient_soundness_scout.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_soundness_scout.md` |
| `vendor/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `vendor/complete85_reduced_auxiliary_degree.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.json` |
| `vendor/complete85_reduced_auxiliary_degree.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` |
| `vendor/complete86_factored_first_root.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_factored_first_root.md` |
| `vendor/complete86_ordinary_auxiliary_projection.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_ordinary_auxiliary_projection.json` |
| `vendor/complete86_ordinary_auxiliary_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_ordinary_auxiliary_projection.md` |
| `vendor/complete86_transport_quotient_shear.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` |
| `vendor/complete92_norm_unit_guard.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete92_norm_unit_guard.json` |
| `vendor/complete92_norm_unit_guard.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete92_norm_unit_guard.md` |
| `vendor/explore_fixed_raw_universal_76.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py` |
| `vendor/explore_fixed_raw_universal_78.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_78.py` |
| `vendor/explore_fixed_raw_universal_81.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_81.py` |
| `vendor/explore_fixed_unary_tableau.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_unary_tableau.py` |
| `vendor/explore_helical_unary_tableau.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_helical_unary_tableau.py` |
| `vendor/explore_marked_periodic_tm_padding.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_marked_periodic_tm_padding.py` |
| `vendor/explore_three_cell_period_lift.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_three_cell_period_lift.py` |
| `vendor/k215.pinned.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `vendor/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `vendor/review_complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_scaled_strong_output.md` |
| `vendor/review_complete84_signed_quotient_soundness.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_signed_quotient_soundness.json` |
| `vendor/review_complete84_signed_quotient_soundness.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_signed_quotient_soundness.md` |
| `vendor/review_complete85_auxiliary_bezout_math.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete85_auxiliary_bezout_math.md` |
| `vendor/review_complete85_auxiliary_bezout_source.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete85_auxiliary_bezout_source.md` |
| `vendor/review_complete86_ordinary_auxiliary_math.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete86_ordinary_auxiliary_math.md` |
| `vendor/review_complete86_ordinary_auxiliary_source.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete86_ordinary_auxiliary_source.md` |
| `checks/SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |

## `04-poly73/` (`zfc_diophantine (1).zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `data/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `provenance/upstream/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `provenance/upstream/K215_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/NOTICE.md` |
| `provenance/upstream/K215_VERIFICATION_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `provenance/upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `provenance/upstream/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `provenance/upstream/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `provenance/upstream/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `provenance/upstream/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `provenance/upstream/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `src/upstream/complete75_half_binomial_compiler.py` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py` |
| `src/upstream/explore_fixed_raw_universal_76.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py` |
| `SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |

## `05-fixed15-16/` (`ZFC_Diophantine_15_16_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `arithmetic/upstream_complete84.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `coefficients/canonicalization.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/canonicalization.json` |
| `coefficients/k215.native.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm` |
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `notices/k215/licenses/SOURCE_PINS.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/SOURCE_PINS.json` |
| `notices/k215/provenance/partial-selector/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/ATTRIBUTION.md` |
| `notices/k215/provenance/partial-selector/provenance/k217-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/NOTICE.md` |
| `notices/k215/provenance/partial-selector/provenance/parent-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `notices/k215/provenance/permuted-commands/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/ATTRIBUTION.md` |
| `notices/k215/provenance/permuted-commands/provenance/K218_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/parent-NOTICE.md` |
| `notices/k215/provenance/permuted-commands/provenance/PREDECESSOR_ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `references/EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `references/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `references/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `references/FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `references/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `references/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `references/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `references/complete84_signed_quotient_absorption.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_absorption.md` |
| `references/complete84_signed_quotient_soundness_scout.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_signed_quotient_soundness_scout.md` |
| `references/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `references/complete85_reduced_auxiliary_degree.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` |
| `references/complete92_norm_unit_guard.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete92_norm_unit_guard.md` |
| `references/k215_candidate_README.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md` |
| `references/k215_candidate_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `references/k215_verification_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `references/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `references/review_complete84_signed_quotient_soundness.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_signed_quotient_soundness.md` |
| `references/review_complete85_auxiliary_bezout_math.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete85_auxiliary_bezout_math.md` |

## `06-blank67/` (`zfc_diophantine_67.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `upstream/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` |
| `upstream/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v` |
| `upstream/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table215.v` | `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table215.v` |
| `upstream/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/BASE_TWO_PELL_89_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/BASE_TWO_PELL_89_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_factored_first_root.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_factored_first_root.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` |
| `upstream/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |

## `07-fixed70/` (`zfc_diophantine_fixed70.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `artifacts/compiler/K215_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/NOTICE.md` |
| `artifacts/compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `artifacts/compiler/licenses/SOURCE_PINS.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/SOURCE_PINS.json` |
| `artifacts/compiler/provenance/partial-selector/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/ATTRIBUTION.md` |
| `artifacts/compiler/provenance/partial-selector/provenance/k217-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/NOTICE.md` |
| `artifacts/compiler/provenance/partial-selector/provenance/parent-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `artifacts/compiler/provenance/permuted-commands/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/ATTRIBUTION.md` |
| `artifacts/compiler/provenance/permuted-commands/provenance/K218_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/parent-NOTICE.md` |
| `artifacts/compiler/provenance/permuted-commands/provenance/PREDECESSOR_ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `artifacts/compiler/provenance/permuted-commands/provenance/inputs.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/inputs.json` |
| `artifacts/compiler/provenance/permuted-commands/provenance/source_proof_review.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/provenance/permuted-commands/provenance/source_proof_review.json` |
| `artifacts/compiler/provenance/permuted-commands/provenance/source_proof_review.md` | `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/159-permuted-provenance-source_proof_review.md` |
| `artifacts/compiler/provenance/permuted-commands/sections/source_calibration.tex` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/gc-zc215/proofs/inherited_calibration.tex` |
| `artifacts/parent84_reference.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |

## `08-start-only67/` (`diophantine_zfc_cdd582b.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `evidence/diophantine_zfc_compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `evidence/diophantine_zfc_core/sources/Code254.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean` |
| `evidence/diophantine_zfc_core/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `evidence/diophantine_zfc_core/sources/Enum222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum222.lean` |
| `evidence/diophantine_zfc_core/sources/KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` |
| `evidence/diophantine_zfc_core/sources/KDense215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean` |
| `evidence/diophantine_zfc_core/sources/KEind222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean` |
| `evidence/diophantine_zfc_core/sources/KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` |
| `evidence/diophantine_zfc_core/sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `evidence/diophantine_zfc_core/sources/KLowerQHyp.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean` |
| `evidence/diophantine_zfc_core/sources/KQ1ZF.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` |
| `evidence/diophantine_zfc_core/sources/KSeed222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeed222.lean` |
| `evidence/diophantine_zfc_core/sources/KTable215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean` |
| `evidence/diophantine_zfc_core/sources/KTableCore.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTableCore.lean` |
| `evidence/diophantine_zfc_core/sources/KThmK.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KThmK.lean` |
| `evidence/diophantine_zfc_core/sources/KUpper222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` |
| `evidence/diophantine_zfc_core/sources/TarskiCalculus.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiCalculus.lean` |
| `evidence/diophantine_zfc_core/sources/WFModel.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModel.lean` |
| `evidence/diophantine_zfc_core/sources/WellFoundedPart.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPart.lean` |
| `evidence/diophantine_zfc_core/sources/ZFModels.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ZFModels.lean` |
| `evidence/diophantine_zfc_core/sources/k215.native.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm` |
| `evidence/diophantine_zfc_core/sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `evidence/diophantine_zfc_encoding/k230.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k228/ingredients/k230.tm` |
| `evidence/diophantine_zfc_review/Lean__MRDP.md` | `Computability/HilbertTenthProblem/Lean/MRDP.md` |
| `evidence/diophantine_zfc_review/Lean__README.md` | `Computability/HilbertTenthProblem/Lean/README.md` |
| `evidence/diophantine_zfc_review/Papers__1980__EXPLORATION_FIXED_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` |
| `evidence/diophantine_zfc_review/Papers__1980__EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_77_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_80_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_80_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_82_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_82_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_84_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_84_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__FIXED_RAW_UNIVERSAL_88_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_88_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1980__PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `evidence/diophantine_zfc_review/Papers__1982__jones1982_corrected.tex` | `Computability/HilbertTenthProblem/Papers/1982/jones1982_corrected.tex` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete74_factored_first_norm.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.json` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete74_factored_first_norm.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_half_binomial.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial.json` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_half_binomial_compiler.py` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_norm_product89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product89.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete75_signed_projection_elimination101.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete84_scaled_strong_output.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete84_scaled_strong_output.py` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.py` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete86_factored_first_root.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_factored_first_root.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__complete86_transport_quotient_shear.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `evidence/diophantine_zfc_review/Papers__research-wip__native-stream-queue__review_complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete84_scaled_strong_output.md` |
| `evidence/diophantine_zfc_review/Papers__verification__explore_fixed_raw_universal_75.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_75.py` |
| `evidence/diophantine_zfc_review/Papers__verification__explore_fixed_raw_universal_76.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py` |
| `evidence/diophantine_zfc_review/Papers__verification__explore_fixed_raw_universal_77.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_77.py` |
| `evidence/diophantine_zfc_review/Papers__verification__explore_fixed_raw_universal_78.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_78.py` |
| `evidence/diophantine_zfc_review/Papers__verification__explore_fixed_raw_universal_80.py` | `Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_80.py` |
| `evidence/diophantine_zfc_review/README_HilbertTenthProblem.md` | `Computability/HilbertTenthProblem/README.md` |
| `SHA256SUMS` | not staged: checksum ledger (`.gitignore`) |
