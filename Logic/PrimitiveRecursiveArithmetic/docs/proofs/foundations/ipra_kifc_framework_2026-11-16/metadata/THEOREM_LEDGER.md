# KIFC theorem and claim ledger - second edition

Status vocabulary:

- **Inherited checked**: inspected upstream theorem concludes `Prf PRAAx` (or
  is part of the checked logical presentation) and is covered by repository
  build/axiom-audit records.
- **Source-complete uncompiled**: no intentional proof hole in the supplied
  adapter source, but the artifact environment could not run Lean.
- **Human-complete**: detailed ordinary mathematical proof in the report.
- **Finite-tested**: exact finite reference algorithm covered by deterministic
  tests; this is not an object proof.
- **Lean interface**: definitions, signatures, dependencies, and completion
  path, but no completed proof term.
- **Placeholder-bearing blueprint**: exact theorem decomposition with explicit
  `sorry` markers; never claimed checked.
- **Conditional producer**: generic verifier/composition theorem is complete
  under explicitly named quantitative data.
- **Open**: a mathematical or formalization obligation remains.

| ID | Claim | Report | Status | Artifact |
|---|---|---|---|---|
| K1 | Deterministic contract composition | Sec. 4 | Human-complete | report |
| K2 | Kernel proof schedule compilation | Sec. 7, 14, 15 | Human-complete; source-complete uncompiled | `KernelCore.lean` |
| K3 | Loop-certificate compilation via `IPRA.ind` | Sec. 6, 14, 15 | Human-complete; source-complete uncompiled | `KernelCore.lean` |
| K4 | Booleanization of fixed bounded formulas | Sec. 5 | Human-complete; Lean interface | `BooleanBlueprint.lean` |
| K5 | Least bounded search | Sec. 5, 15 | Inherited checked backend; finite-tested; adapter outline | upstream `Core/Search.lean`, Python, `SearchBlueprint.lean` |
| K6 | Bounded-existential normal form | Sec. 5 | Human-complete; Lean interface | `BoundedExistentialBlueprint.lean` |
| K7 | One-loop normal form | Sec. 6 | Human-complete metaconstruction | report |
| K8 | Least reverse demand on a DAG | Sec. 4 | Human-complete; finite-tested | Python |
| K9 | Kernel-integrated graph compilation | Sec. 7 | Human-complete relative to local certificates; generator open | report + `GraphBlueprint.lean` |
| K10 | Viability iff compatible finite suffix | Sec. 8 | Human-complete; finite-tested; Lean interface | Python + `RelationalBlueprint.lean` |
| K11 | Least viable path / finite dependent choice | Sec. 8 | Human-complete; finite-tested; Lean interface | Python |
| K12 | Exact stable-observer elimination | Sec. 9 | Human-complete; finite-tested; Lean interface | Python |
| K13 | Diameter-stable elimination | Sec. 9 | Human-complete; finite-tested | Python |
| K14 | Shrinking-cloud regular name | Sec. 9 | Human-complete conditional producer theorem | report + Python budgets |
| K15 | Guarded totalization | Sec. 10 | Human-complete | report |
| K16 | Finite-net transfer and finite gluing | Sec. 10 | Human-complete conditional producer theorems | report |
| K17 | Height bound iff complete finite list | Sec. 12 | Human-complete; finite-tested | report + Python |
| K18 | Polynomial algebra node via `ipra_ring` | Sec. 11 | Inherited checked backend; adapter outline | `Examples.lean` |
| K19 | Negative syntax/substitution/axiom layer | Sec. 12 | Inherited repository source/build evidence | upstream `NegativeSyntax.lean` |
| K20 | Stability of all translated formulas | Sec. 12 | Human-complete; placeholder-bearing Lean blueprint | `RetainedTransferBlueprint.lean` |
| K21 | Translation of classical PRA derivations | Sec. 12 | Human-complete; placeholder-bearing Lean blueprint | `RetainedTransferBlueprint.lean` |
| K22 | QF and retained recovery | Sec. 12 | Human-complete; syntax finite-tested; placeholder-bearing Lean blueprint | Python + `RetainedTransferBlueprint.lean` |
| K23 | Retained classical-to-intuitionistic transfer | Sec. 12 | Human-complete; placeholder-bearing Lean blueprint | report + Lean blueprint |
| K24 | Transfer through `pra_iff_native` | Sec. 14 | Inherited checked | upstream source audit |
| B1 | No total universal PR evaluator | Sec. 7 | Human-complete barrier | report |
| B2 | No unguarded exact branch selector at collision | Sec. 13 | Constructive/computability barrier | report |
| B3 | Metastability does not yield a modulus in general | Sec. 9, 13 | Computability barrier | report |
| B4 | Finiteness alone does not yield a cutoff | Sec. 13 | Human-complete halting reduction | report |
| B5 | Negative nonzero does not yield apartness uniformly | Sec. 10, 13 | Constructive/computability barrier | report |
