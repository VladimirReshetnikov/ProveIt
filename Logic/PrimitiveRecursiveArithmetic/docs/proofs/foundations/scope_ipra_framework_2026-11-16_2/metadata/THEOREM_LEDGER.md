# Theorem ledger

| Result | Status | Evidence |
|---|---|---|
| Ordinary `Prf PRAAx` calculus and structural rules | upstream checked | `ConciseIPRA/Deduction.lean` |
| QF induction and arbitrary-term instantiation | upstream checked | `IPRADerivations/Core/Basic.lean` |
| `PTm.toPR`, `recDef` | upstream checked | `IPRADerivations/Core/Definitions.lean` |
| One-parameter bounded search | upstream checked | `IPRADerivations/Core/Search.lean` |
| Scoped realization | human-complete; kernel candidate | direct `Prf.exE`; `lean/SCOPE/Kernel.lean` |
| Conditional producer boundary | human-complete; kernel candidate | `Prf.impI` + `Prf.exE` |
| Arity-generic least-zero search | human-complete reduction; Lean work | report Theorem 6.2 |
| Schema-first bounded reflection | human-complete; Lean blueprint | report Theorem 6.3 and Sections 7-9 |
| Open substitution coherence | human-complete | fixed-symbol construction + upstream syntax laws |
| Least accepted code | human-complete; Lean blueprint | report Theorem 8.3 |
| Exact/quotient/metric observer elimination | human-complete schema | report Section 10 |
| Scope-minimal normal form | human-complete metatheorem | report Theorem 11.1 |
| Indexed plan compiler | human-complete; Lean blueprint | report Theorem 12.1 |
| Deterministic trace invariant | human-complete | report Theorem 13.1 |
| Capped cyclic demand closure | human-complete; executable test | report Theorem 13.2 |
| Backward viability and whole path | human-complete schema | report Section 13.4 |
| Python reference suite | executable only | 16 passing tests |
| General height/modulus/cover producers | not supplied | explicit residuals |
| Exact selector through collisions | deliberately not claimed | gap guard or relational reformulation required |

No theorem labelled “blueprint” or “candidate” is represented as kernel-checked.
