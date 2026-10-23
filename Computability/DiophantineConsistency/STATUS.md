# Research status

Updated 23 October 2026. This is a work log, not a completion certificate.

| Component | Status | Evidence / next task |
|---|---|---|
| Reports and historical comparison | Initial audit complete | Wave-5 collection README; P67 circuit in package 36 |
| Exact meaning of consistency | Identified | `¬ BProv ZFCax_s [] Form.fBot`; existing unconditional K215 endpoint |
| Concrete recursively enumerable refutation predicate | In progress | Check a register or zipper-machine interpreter and its computability |
| Nine-variable specialization | In progress | Specialize the proved Jones representation at positive input 1 |
| Quartic alternative | In progress | Specialize `rePred_quartic58` without raising total degree |
| Explicit, computable coefficient recipe | Open | Do not confuse classical selection with coefficient export |
| P67 compiler correctness in Lean | Open | The report's ordinary proof is not yet a Lean proof |
| Object-level ZFC derivation | Open | External equivalence and internal provability are separate claims |
| Global simplicity minimum | Not claimed | No common ordering of all size measures; no optimality theorem |
| Short-equation local simplification | Lean checked | `ShortEquation.scaled_zero_iff_reduced`, no compiler hypothesis |

## Validation environment

The checkout uses Lean `v4.32.0` and Mathlib `v4.32.0`. It initially has no
local `.lake` directory. Existing machine-verification and Mathlib caches
are being inspected so a fresh check can reuse matching dependencies
without copying large unrelated builds.

## Checked local simplification

`Lean/DiophantineConsistency/ShortEquation.lean` compiles under Lean 4.32.0.
`Lean/checks/ShortEquationAxioms.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for its main equivalence. The ring
identity uses only `propext` and `Quot.sound`.

The theorem proves cancellation of the nonzero discriminant and reduction
of the auxiliary coefficient. Its crucial premise is proved modulo 4:
`f² - ((a+2)²-1)t² ≠ -1`. An integer product equal to 1 therefore forces
this factor to be +1, which justifies the coefficient replacement in both
directions. This is an equality of complete zero sets, not a comparison of
sample evaluations.

It supports a candidate 69-operation, degree-111 evaluator of the inherited
15-positive-variable equation. The initial 68-operation estimate missed
the old evaluator's shared multiplication `Δ*f²`; the corrected ledger is
being emitted independently. Compiler correctness and its connection to
ZFC have not been inferred from this local theorem.
