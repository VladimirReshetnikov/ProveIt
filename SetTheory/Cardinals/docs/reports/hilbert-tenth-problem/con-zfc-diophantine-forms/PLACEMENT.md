# Placement record: batch 219 (wave 3)

Intake record, not a delivered file. The eight archives of the arrival
commit `cbf94cb552` ("Con(ZFC) in Diophantine form (wave-3)") were extracted
straight from the committed ZIPs into numbered directories 16–23, with the
single wrapper directory removed. Nothing was edited
and nothing was run at intake.

**Wave 2 is superseded.** By Vladimir's direction the wave-3 packages
supersede the seven batch-218 packages, so directories `09-…` to
`15-…` were removed from the tree in the same commit. They remain
recoverable from placement `8a4b00b5bf` (or any commit up to the one before
this placement), whose own `PLACEMENT.md` maps their omitted members; their
archives remain in arrival `7be2780f26`. Wave 1 (batch 217) was superseded
earlier; see `084e120830` and arrival `2fd49a1a9d`.

Members not in this tree:

- **Copies of repository files.** A member byte-identical (up to line ends)
  to a blob at the placement parent *outside this report* is omitted; the
  tables below name the shortest repository path holding the same bytes.
  Wave-3 copies of wave-2 files are therefore kept, since wave 2 leaves the
  tree. Licence and notice files are always kept. All eight packages pin
  `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.
- **Checksum ledgers and logs.** `SHA256SUMS*` and `*.log` are excluded by
  the root `.gitignore`; they were not verified.

The delivered verification drivers read their vendored copies at the
delivered paths. To rerun a package, extract its archive from the arrival
commit into a scratch directory and run it there:

```sh
git show cbf94cb552:'docs/incoming/<archive>.zip' > /tmp/<archive>.zip
```

| Dir | Archive | Members | Placed | Omitted copies | Ignored | Wrapper |
|---|---|---:|---:|---:|---:|---|
| `16-integer27/` | `con_zfc_27_integer_synthesis_2026-10-22.zip` | 50 | 46 | 4 | 0 | `con_zfc_27_integer_synthesis/` |
| `17-primitive12/` | `ProveIt_ConZFC_Primitive12_2026-10-22.zip` | 80 | 67 | 12 | 1 | `con_zfc_primitive12/` |
| `18-jones9/` | `ProveIt_ConZFC_9_12_27_2026-10-22.zip` | 173 | 100 | 61 | 12 | `con_zfc_9_12_27/` |
| `19-wang943/` | `twelve-variable-con-zfc.zip` | 288 | 286 | 1 | 1 | `twelve-variable-con-zfc/` |
| `20-root12/` | `ZFC_Diophantine_Twelve_Variables_2026-10-22.zip` | 121 | 115 | 5 | 1 | `ZFC_Diophantine_Twelve_Variables/` |
| `21-norm12/` | `con-zfc-norm12-2026-10-22.zip` | 64 | 60 | 3 | 1 | `con-zfc-norm12/` |
| `22-monic12/` | `ProveIt_ConZFC_Monic12_2026-10-22.zip` | 59 | 56 | 3 | 0 | `con_zfc_synthesis/` |
| `23-separating12/` | `con-zfc-twelve-2026-10-22.zip` | 86 | 81 | 4 | 1 | `con-zfc-twelve-2026-10-22/` |

Total: 921 members.

## `16-integer27/` (`con_zfc_27_integer_synthesis_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/K215_CALIBRATION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/K215_VERIFICATION.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |

## `17-primitive12/` (`ProveIt_ConZFC_Primitive12_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `inherited/ASYMMETRIC_SCALE.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `inherited/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `inherited/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `inherited/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `inherited/HALF_BINOMIAL_KERNEL.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `inherited/K215_CALIBRATION_PROOF.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `inherited/K215_VERIFICATION_STATUS.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `inherited/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `inherited/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `machine/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `machine/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `SHA256SUMS` | not staged: checksum ledger |

## `18-jones9/` (`ProveIt_ConZFC_9_12_27_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `upstream/K215_README.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/lean/BusyBeaver/ZFC/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `upstream/lean/Diophantine/Common/RadicalBounds.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RadicalBounds.lean` |
| `upstream/lean/Diophantine/Common/RadicalField.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RadicalField.lean` |
| `upstream/lean/Diophantine/Common/RadicalIndependence.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RadicalIndependence.lean` |
| `upstream/lean/Diophantine/Common/RadicalWeights.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RadicalWeights.lean` |
| `upstream/lean/Diophantine/Common/RefinedRelationCombining.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RefinedRelationCombining.lean` |
| `upstream/lean/Diophantine/Common/RefinedRelationCombiningArithmetic.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RefinedRelationCombiningArithmetic.lean` |
| `upstream/lean/Diophantine/Common/RefinedRelationCombiningBounds.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RefinedRelationCombiningBounds.lean` |
| `upstream/lean/Diophantine/Common/RefinedRelationCombiningDegree.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RefinedRelationCombiningDegree.lean` |
| `upstream/lean/Diophantine/Common/RefinedRelationCombiningPolynomial.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RefinedRelationCombiningPolynomial.lean` |
| `upstream/lean/Diophantine/Common/RelationCombining.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RelationCombining.lean` |
| `upstream/lean/Diophantine/Common/RelationCombiningArithmetic.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RelationCombiningArithmetic.lean` |
| `upstream/lean/Diophantine/Common/RelationCombiningBounds.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RelationCombiningBounds.lean` |
| `upstream/lean/Diophantine/Common/RelationCombiningPolynomial.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RelationCombiningPolynomial.lean` |
| `upstream/lean/Diophantine/Common/SignInvariantPolynomial.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Common/SignInvariantPolynomial.lean` |
| `upstream/lean/Diophantine/Paper1982/Coding.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Coding.lean` |
| `upstream/lean/Diophantine/Paper1982/EnumerationQuartic.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/EnumerationQuartic.lean` |
| `upstream/lean/Diophantine/Paper1982/Index.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Index.lean` |
| `upstream/lean/Diophantine/Paper1982/Master1.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master1.lean` |
| `upstream/lean/Diophantine/Paper1982/NineMain.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean` |
| `upstream/lean/Diophantine/Paper1982/NinePoly.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NinePoly.lean` |
| `upstream/lean/Diophantine/Paper1982/NineRatio.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` |
| `upstream/lean/Diophantine/Paper1982/NineReduce.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean` |
| `upstream/lean/Diophantine/Paper1982/Section4.lean` | `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Section4.lean` |
| `upstream/machine/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/machine/licenses/SOURCE_PINS.json` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/licenses/SOURCE_PINS.json` |
| `upstream/machine/proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `upstream/machine/provenance/partial-selector/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/ATTRIBUTION.md` |
| `upstream/machine/provenance/partial-selector/provenance/k217-NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/NOTICE.md` |
| `upstream/machine/provenance/partial-selector/provenance/parent-ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `upstream/machine/provenance/permuted-commands/provenance/ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/permuted/provenance/ATTRIBUTION.md` |
| `upstream/machine/provenance/permuted-commands/provenance/K218_NOTICE.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k216/provenance/parent-NOTICE.md` |
| `upstream/machine/provenance/permuted-commands/provenance/PREDECESSOR_ATTRIBUTION.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k217/provenance/ATTRIBUTION.md` |
| `upstream/math/1980/BASE_TWO_PELL_89_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/BASE_TWO_PELL_89_PROOF.md` |
| `upstream/math/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| `upstream/math/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| `upstream/math/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` |
| `upstream/math/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md` |
| `upstream/math/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` | `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md` |
| `upstream/math/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md` |
| `upstream/math/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| `upstream/math/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` |
| `upstream/math/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` |
| `upstream/math/1980/HALF_PARAMETER_PELL_92_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md` |
| `upstream/math/1980/PELL_RELAXED_AUXILIARY_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md` |
| `upstream/math/1980/PELL_SIGNED_PROOF.md` | `Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_normalized_strong87.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_normalized_strong87.md` |
| `upstream/math/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md` |
| `upstream/math/research-wip/native-stream-queue/complete84_scaled_strong_output.json` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json` |
| `upstream/math/research-wip/native-stream-queue/complete84_scaled_strong_output.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.md` |
| `upstream/math/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md` |
| `upstream/math/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_reduced_auxiliary_degree.md` |
| `upstream/math/research-wip/native-stream-queue/complete86_factored_first_root.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_factored_first_root.md` |
| `upstream/math/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_transport_quotient_shear.md` |
| `upstream/math/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md` |
| `upstream/math/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` | `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md` |
| `verification/base.log` | not staged: log file (`*.log`) |
| `verification/fixed_coefficients.log` | not staged: log file (`*.log`) |
| `verification/integer27.log` | not staged: log file (`*.log`) |
| `verification/latex-pass-1.log` | not staged: log file (`*.log`) |
| `verification/latex-pass-2.log` | not staged: log file (`*.log`) |
| `verification/nine_build.log` | not staged: log file (`*.log`) |
| `verification/nine_checks.log` | not staged: log file (`*.log`) |
| `verification/nine_fixed_instance.log` | not staged: log file (`*.log`) |
| `verification/t4_enumeration.log` | not staged: log file (`*.log`) |
| `verification/t4_independent.log` | not staged: log file (`*.log`) |
| `verification/twelve_build.log` | not staged: log file (`*.log`) |
| `verification/twelve_checks.log` | not staged: log file (`*.log`) |

## `19-wang943/` (`twelve-variable-con-zfc.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `compiler/upstream/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `SHA256SUMS.txt` | not staged: checksum ledger |

## `20-root12/` (`ZFC_Diophantine_Twelve_Variables_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `coefficients/sources/t4-bridge/sources/ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` |
| `coefficients/sources/t4-bridge/sources/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `coefficients/sources/t4-bridge/sources/ordinary_k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `requirements.txt` | `Algebra/SurrealNumbers/docs/surreal/gamma-functions/data/requirements.txt` |
| `SHA256SUMS.json` | not staged: checksum ledger |

## `21-norm12/` (`con-zfc-norm12-2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/sources/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `upstream/K215_VERIFICATION.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |
| `upstream/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `SHA256SUMS` | not staged: checksum ledger |

## `22-monic12/` (`ProveIt_ConZFC_Monic12_2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `data/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `reference/k215_proof.md` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` |
| `reference/k215_verification.md` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` |

## `23-separating12/` (`con-zfc-twelve-2026-10-22.zip`)

| Delivered member | Same bytes in the repository |
|---|---|
| `coefficients/KEndpoint215.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` |
| `coefficients/inherited_lean_endpoint_compiler.log` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean/EndpointAudit215.log` |
| `coefficients/inherited_rocq_endpoint.log` | `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/rocq/actual/K215F.Correct215.log` |
| `coefficients/k215.tm` | `Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm` |
| `verification/latex_build.log` | not staged: log file (`*.log`) |
