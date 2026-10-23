# Independent intake audit, 23 October 2026

Repository snapshot: `4b4349064a750ba6347293b55874a7f92abdd0db`.
All eight incoming archives were read from this snapshot and extracted to `work_audit/incoming/<archive-stem>/<wrapper>/`. The extraction checked against absolute paths and parent traversal. No remote mutation was made.

## Current claimed frontier that a new delivery must compare against

These are package claims. The strongest selective package and the squared-modulus short circuits were replayed as specified below; the other values were read from their entry points and proof documents.

| Criterion | Supplied domain | Degree | Binary operations | Incoming archive |
|---|---|---:|---:|---|
| Fewest-degree nine-variable form | 9 positive | 7,344,328 | 738 | ZFC_Diophantine_Selective_Quadratic_2026-10-23 |
| Nine-variable low-cost form | 9 positive | 15,502,748 | 548 | con-zfc-sparse-pell-124c07c0b7 |
| Nine-variable compromise | 9 positive | 10,486,092 | 603 | con-zfc-sparse-pell-124c07c0b7 |
| Nine-variable other tradeoff | 9 positive | 10,127,484 | 655 | con-zfc-sparse-pell-124c07c0b7 |
| Fewest-degree ten-integer form | 10 unrestricted integers | 21,111,400 | 659 | ZFC_Diophantine_Selective_Quadratic_2026-10-23 |
| Ten-integer low-cost form | 10 unrestricted integers | 50,822,936 | 582 | con-zfc-sparse-pell-124c07c0b7 |
| Ten-integer compromise | 10 unrestricted integers | 34,378,296 | 637 | con-zfc-sparse-pell-124c07c0b7 |
| Non-Sun signed form | 13 unrestricted integers | 57,866,184 | 759 | ZFC_Diophantine_Selective_Quadratic_2026-10-23 |
| Eleven-positive form | 11 positive | 954 | 113 | con-zfc-sparse-pell-124c07c0b7 |
| Twelve-positive form | 12 positive | 897 | 108 | con-zfc-sparse-pell-124c07c0b7 |
| Fourteen-positive form | 14 positive | 56 | 79 | ConZFC_Support_Sensitive_2026-10-23 |
| Degree-44 short form | 15 positive | 44 | 75 | ConZFC_Sparse_Support_2026-10-23 |
| Smallest arbitrary-degree operation count | 15 positive | 157 | 66 | con_zfc_sparse_arithmetic_2026-10-23 |
| Short SOS tradeoff | 15 positive | 80 | 72 | con_zfc_sparse_arithmetic_2026-10-23 |
| Short SOS tradeoff | 15 positive | 68 | 74 | con_zfc_sparse_arithmetic_2026-10-23 |

The original 67-operation degree-155 polynomial remains nondominated against 66/157; similarly 69/111 against68/113. The active repository also has a Lean-checked local 76/64 candidate. The 59-operation seven-equation system is a different metric and domain size.

The package table is not an exhaustive Pareto frontier over every circuit in all eight archives. It is sufficient to prevent comparing only against stale wave5/6 summaries or claiming a record already present in wave7.

## Actual replay evidence

`ZFC_Diophantine_Selective_Quadratic/.../verify.py` completed successfully:21 finite stages,49 byte-identical rebuilt files,279 sealed files. This includes source support isolation, sparse signed-borrow padding, calibrated block threshold, nine-variable exact degree, ten-integer and thirteen-integer source checks, and positive/short adapters.

`con_zfc_sparse_arithmetic.../short/build_and_audit.py` completed successfully: four literal circuits66/157,68/113,72/80,74/68, all live; exact local pullback and main norm identities;24 auxiliary reconstruction examples;100 modular full-circuit diagnostics per variant. These checks are finite, not an unbounded semantic proof.

## Proof audit findings

1. Selective nine-variable proof: no fatal flaw found in the reviewed new arithmetic. It explicitly proves unconditional positivity of Dcode,R,N and all Jones numerical hypotheses before invoking the ratio theorem; it distinguishes L from N; it proves signed carries stay in{-1,0}; and it forces a square threshold by an actual identity in power-of-two base exponents. The two-root finalizer proves rational roots integral without an unjustified square-class-independence assumption. Coefficient tuple binding is explicit.
2. Its improved source uses original package31 transport, not package45's shifted transport. The support is common but coefficients differ; any recombination must rebuild the exact coefficient rows and derived leaves.
3. The66-operation proof is a complete new-witness reconstruction rather than tuplewise equivalence. Soundness is the exact identity P66(f,T)=P67(f,fT). Completeness proves an odd Chebyshev quotient congruence modulo f^2 and uses the calibrated native phase R=3mod4. It does not claim every old auxiliary quotient is divisible by f. The argument appears sound under its inherited compiler/Pell contracts.
4. The degree44/75 minimum construction has a local minimum proof for three blocks and an additional signed index/transport recovery dependency to combine NkNt=1. Its cleaner degree44/76 variant keeps separate comparisons and has a local tuplewise equivalence. These scopes must not be conflated.

## Formal status at the actual snapshot

`Computability/DiophantineConsistency/EXPLICIT_EQUATION.md` and `STATUS.md` now report closed executable nine-natural and nine-positive coefficient recipes, with external Lean equivalence to the actual syntactic `ConZFC`. Coefficients of those generic recipes have not been materialized and their final sizes are not measured.

`OBJECT_ZFC.md` explicitly says the object-language consistency and unsolvability sentences and their `BProv` iff derivation have not been assembled. The external Lean equivalence is not itself an object-language ZFC derivation. Ordinary mathematical formalizability in ZFC can support a paper theorem, but a new deliverable should not claim that this formal derivation has already been exported.

All incoming small literal circuits still rely on inherited unbounded native-window compiler/calibration theorems and ordinary Pell/Jones interfaces. No new end-to-end kernel proof accompanies them. Every ten-integer branch also inherits Sun's2026 theorem; nine-positive and13-integer Jones routes avoid it.

## Promising combinations not yet claimed in the reviewed packages

- Transfer the sparse-pell cheaper positivity-first/sharper-majorant finalizer to the selective package's calibrated popcount source, after explicitly checking every numerical source contract and coefficient-row convention. This may reduce the operation cost and/or degree of the current best7,344,328/738 point.
- Transfer the squared-modulus auxiliary quotient substitution to active P76's residual shear: its known pullback should lower76/64 to75/64 because the auxiliary degree rises only to30 while the strong degree32 remains dominant. This is a modest concrete improvement, not a major breakthrough.
- A substantially smaller source certificate could improve few-variable degree, but any novelty claim must clear wave7's already combined supported-pair isolation, irregular target overlap, sparse signed padding, popcount calibration, and near-square majorant. Merely rediscovering these changes is not a new contribution.
