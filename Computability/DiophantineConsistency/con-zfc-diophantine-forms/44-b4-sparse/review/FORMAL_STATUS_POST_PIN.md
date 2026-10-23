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

## Validation environment

The checkout uses Lean `v4.32.0` and Mathlib `v4.32.0`. It initially has no
local `.lake` directory. Existing machine-verification and Mathlib caches
are being inspected so a fresh check can reuse matching dependencies
without copying large unrelated builds.

No new Lean theorem has yet been reported as checked in this research.
