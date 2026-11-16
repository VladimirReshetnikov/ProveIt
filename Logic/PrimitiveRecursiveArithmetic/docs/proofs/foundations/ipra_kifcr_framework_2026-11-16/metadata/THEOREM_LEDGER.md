# KIFC-R theorem and claim ledger

Status vocabulary:

- **Inherited checked** — current upstream theorem has endpoint `Prf PRAAx`.
- **Human-complete** — detailed ordinary mathematical proof in the PDF.
- **Finite-tested** — exact reference algorithm has passing tests.
- **Lean outline** — definitions, signatures, dependencies, and completion path.
- **Conditional** — verifier/composition theorem is proved relative to explicit
  producer formulas.
- **Open** — mathematical producer or checked implementation remains.

| ID | Claim | Report | Status | Artifact |
|---|---|---|---|---|
| R1 | Local-rule and proof-schedule composition | §§3,7 | Human-complete; Lean outline | `KernelCore.lean` |
| R2 | Loop certificate via `IPRA.ind`/`inst` | §§6,14 | Human-complete; Lean outline | `KernelCore.lean` |
| R3 | Fixed bounded-formula Booleanization | §5 | Human-complete; Lean outline | `BooleanBlueprint.lean` |
| R4 | Least bounded zero search | §5 | Inherited checked; adapter tested/outlined | upstream `Core.Search`; Python; `SearchAdapterBlueprint.lean` |
| R5 | Pairing/projections/simultaneous recursion | §§6,14 | Inherited checked | upstream `Core.Pairing` |
| R6 | Residual normalization and conditional graph compilation | §§4–7 | Human-complete; finite-tested; Lean outline | Python; `ResidualBlueprint.lean` |
| R7 | Closure by supplied residual producers | §4b | Human-complete; direct `Prf.trans` outline | `KernelCore.lean` |
| R8 | Least acyclic reverse demand | §4 | Human-complete; finite-tested | Python |
| R9 | Capped cyclic demand closure | §7b | Human-complete; finite-tested; Lean outline | Python; `DemandClosureBlueprint.lean` |
| R10 | One-loop normal form and trace reflection | §6 | Human-complete metaconstruction; Lean outline | `TraceBlueprint.lean` |
| R11 | Residualized kernel graph compilation | §7 | Human-complete relative theorem; generator open | `GraphBlueprint.lean` |
| R12 | Viability iff accepted finite suffix | §8 | Human-complete; brute-force tested; Lean outline | Python; `RelationalBlueprint.lean` |
| R13 | Least viable path | §8 | Human-complete; tested; checked-search route outlined | Python |
| R14 | Exact stable-observer elimination | §9 | Human-complete; tested; Lean outline | Python; `ObserverBlueprint.lean` |
| R15 | Diameter-stable choice erasure | §9 | Human-complete; tested | Python |
| R16 | Regular name from diameter/motion/tail data | §9 | Human-complete conditional theorem; tested budgets | report + Python |
| R17 | Guarded totalization and precision composition | §10 | Human-complete conditional theorem | report |
| R18 | Finite-net transfer and finite gluing | §10 | Human-complete conditional theorem | report |
| R19 | Height-bound/list conversion | §§12–13 | Human-complete under explicit coding assumptions; tested | report + Python |
| R20 | Algebra node through `ipra_ring` | §11 | Inherited checked backend; adapter outline | `Examples.lean` |
| R21 | Native transfer | §14 | Inherited checked | upstream `pra_iff_native` |
| B1 | No total universal PR evaluator | §7 | Human-complete barrier | report |
| B2 | No unguarded exact branch selector at collisions | §13 | Constructive/computability barrier | report |
| B3 | Metastability does not yield a modulus in general | §§9,13 | Computability barrier | report |
| B4 | Finiteness/cardinality does not yield a cutoff | §13 | Human-complete reduction | report |
| B5 | Mere represented nonzero does not yield apartness | §§10,13 | Constructive/computability barrier | report |
