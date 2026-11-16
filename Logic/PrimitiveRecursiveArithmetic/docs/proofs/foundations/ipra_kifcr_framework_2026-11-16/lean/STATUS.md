# Lean status

| Component | Current status |
|---|---|
| `KernelRule.use`, `Schedule.compile`, loop wrapper | Source-oriented definitions against inspected API; not built here |
| `ConditionalTheorem.close` | Source-oriented direct `Prf.trans` construction; not built here |
| Boolean primitives and fixed-formula reflection | Interfaces and proof plan; implementation open |
| Least bounded search | **Inherited checked implementation** in `IPRADerivations.Core.Search`; adapter open |
| Pairing/simultaneous recursion | **Inherited checked implementation** in `Core.Pairing` |
| Residual reachability/deduplication | Python reference tested; Lean metalevel generator open |
| Capped cyclic demand closure | Human proof + Python reference tests; object certificate open |
| Packed trace | Structure and generation plan; object implementation open |
| Viability/path reflection | Human proof + Python brute-force tests; object implementation open |
| Stable observers/tail theorem | Human proof + exact tests; object implementation open |
| Cubic rational bisection | Exact Python benchmark; complete Lean path; object proof open |
| New-module axiom audit | Planned in `KIFCR/Checks.lean`; cannot be run without Lean |

No claim in this packet should be read as a clean Lean build of the new
framework. Inherited checked claims are tied to current repository paths and
the pinned commit. The report clearly separates those claims from new outlines.
