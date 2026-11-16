# Lean status

| Component | Status |
|---|---|
| Upstream API audit | Inspected at pinned commit |
| `KernelRule.use` | Source-complete outline using `Prf.trans` |
| `Schedule.compile` | Source-complete outline using simultaneous cut |
| `LoopCertificate.compile` | Source-complete outline using `IPRA.ind` |
| Algebra adapters | Source-oriented wrappers around inherited checked theorems |
| Boolean primitives/reflection | Interface and implementation plan; not implemented |
| Bounded folds/search | Human proof and object API; generator not implemented |
| Viability/path reflection | Human proof and object API; not implemented |
| Graph generator | Metalevel design only |
| Local Lean build | Not run: Lean unavailable in artifact environment |

No claim in this packet should be read as a clean Lean build of the new KIFC
modules. Existing upstream theorems are reported as inherited checked results
based on the audited repository source and its own axiom-check module.
