# KIFC theorem and claim ledger

Status vocabulary:

- **Inherited checked**: inspected upstream theorem concludes `Prf PRAAx` and
  is included in the upstream axiom audit.
- **Source-complete outline**: no intentional hole, but not compiled here.
- **Human-complete**: detailed ordinary mathematical proof in the report.
- **Finite-tested**: exact finite reference algorithm covered by tests.
- **Lean outline**: definitions, signatures, dependencies, and proof path.
- **Conditional producer**: generic verifier/composition result is complete
  under explicitly named quantitative data.
- **Open**: a mathematical or formalization obligation remains.

| ID | Claim | Report | Status | Artifact |
|---|---|---|---|---|
| K1 | Deterministic contract composition | Sec. 4 | Human-complete | report |
| K2 | Kernel proof schedule compilation | Sec. 7 | Human-complete; source-complete outline | `KernelCore.lean` |
| K3 | Loop-certificate compilation via `IPRA.ind` | Sec. 6, 14 | Human-complete; source-complete outline | `KernelCore.lean` |
| K4 | Booleanization of fixed bounded formulas | Sec. 5 | Human-complete; Lean outline | `BooleanBlueprint.lean` |
| K5 | Least bounded search | Sec. 5 | Human-complete; finite-tested; Lean outline | Python + `SearchBlueprint.lean` |
| K6 | One-loop normal form | Sec. 6 | Human-complete metaconstruction | report |
| K7 | Least reverse demand on a DAG | Sec. 4 | Human-complete; finite-tested | Python |
| K8 | Kernel-integrated graph compilation | Sec. 7 | Human-complete relative to local certificates; graph generator open | report + `GraphBlueprint.lean` |
| K9 | Viability iff finite compatible suffix | Sec. 8 | Human-complete; finite-tested; Lean outline | Python + `RelationalBlueprint.lean` |
| K10 | Least viable path / finite dependent choice | Sec. 8 | Human-complete; finite-tested; Lean outline | Python |
| K11 | Exact stable-observer elimination | Sec. 9 | Human-complete; finite-tested; Lean outline | Python |
| K12 | Diameter-stable elimination | Sec. 9 | Human-complete; finite-tested | Python |
| K13 | Shrinking-cloud regular name | Sec. 9 | Human-complete conditional producer theorem | report + Python budgets |
| K14 | Guarded totalization | Sec. 10 | Human-complete | report |
| K15 | Finite-net transfer and finite gluing | Sec. 10 | Human-complete conditional producer theorems | report |
| K16 | Height bound iff complete finite list | Sec. 12 | Human-complete; finite-tested | report + Python |
| K17 | Polynomial algebra node via `ipra_ring` | Sec. 11 | Inherited checked backend; adapter outline | `Examples.lean` |
| K18 | Transfer through `pra_iff_native` | Sec. 14 | Inherited checked | upstream source audit |
| B1 | No total universal PR evaluator | Sec. 7 | Human-complete barrier | report |
| B2 | No unguarded exact branch selector at collision | Sec. 13 | Constructive/computability barrier | report |
| B3 | Metastability does not yield a modulus in general | Sec. 9, 13 | Computability barrier | report |
| B4 | Finiteness alone does not yield a cutoff | Sec. 13 | Human-complete halting reduction | report |
| B5 | Negative nonzero does not yield apartness uniformly | Sec. 10, 13 | Constructive/computability barrier | report |
