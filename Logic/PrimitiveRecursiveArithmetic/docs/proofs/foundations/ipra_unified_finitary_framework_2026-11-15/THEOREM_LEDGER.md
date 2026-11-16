# Theorem and claim ledger

Status vocabulary:

- **Human-complete**: a full mathematical argument is in the report.
- **Finite-tested**: exact finite instances are checked by the Python suite.
- **Lean-blueprint**: a source-oriented Lean target is supplied but not built.
- **Backend-checked**: inherited from the pinned ProveIt `ConciseIPRA` library.
- **Conditional/open**: depends on an explicitly named producer or estimate.

| ID | Claim | Report location | Status | Lean / executable artifact |
|---|---|---|---|---|
| T1 | Correctness of Boolean `All`, `Any`, and least bounded search | Section 4 | Human-complete; finite-tested | `code/reference_framework.py`; Lean module planned |
| T2 | Structural Booleanization of every fixed bounded formula | Section 4 | Human-complete | Lean compiler planned |
| T3 | Embedded finite-trace reflection from base/step/final `Prf PRAAx` derivations | Section 5 | Human-complete at derivation-constructor level; Lean-blueprint | `lean/TraceCompilerBlueprint.lean` |
| T4 | Finite query-table instantiation and “fix precision, then quantify” | Section 5 | Human-complete | To be layered on T3 |
| T5 | Certificate reflection | Section 5 | Human-complete | To be layered on folds and T3 |
| T6 | Composition of certified transducers | Sections 5 and 9 | Human-complete | Finite-program DSL planned |
| T7 | Viability iff existence of a finite compatible path | Section 7 | Human-complete; finite-tested; Lean-blueprint | `RelationalRefinementBlueprint.lean` |
| T8 | Least viable finite path and finite dependent choice | Section 7 | Human-complete; finite-tested | Python reference implementation |
| T9 | Finite witness amalgamation | Section 7 | Human-complete | Lean object-language migration planned |
| T10 | Full-horizon viability equals forward reachability plus backward viability | Section 7 | Human-complete; finite-tested | Python dynamic program |
| T11 | Shrinking-viability coherence inequality | Section 8 | Human-complete; finite-tested; Lean-blueprint | Python exact square-root clouds; Lean target |
| T12 | Regular-name corollary from a tail modulus | Section 8 | Human-complete | Lean rational metric module planned |
| T13 | Exact label stability from a positive gap | Section 8 | Human-complete | Guarded branch module planned |
| T14 | Precision-contract composition and relational congruence | Section 9 | Human-complete | Compiler/FRP modules planned |
| T15 | Guarded arithmetic of regular names | Section 10 | Human-complete at reusable proof-schema level | `ApplicationTargets.lean` target |
| T16 | Finite-net transfer and approximate minimization | Section 10 | Human-complete | `ApplicationTargets.lean` target |
| T17 | Height bound iff complete finite list for decidable coded points | Section 11 | Human-complete; finite-tested | `ApplicationTargets.lean` target |
| B1 | No total primitive-recursive universal evaluator | Section 15 | Human-complete diagonal proof | Not an implementation target |
| B2 | Cardinality bound does not yield a search cutoff | Section 15 | Human-complete halting reduction | Retained barrier |
| B3 | Exact sign/side selection yields LLPO | Section 15 | Human-complete reduction | Retained barrier |
| B4 | Exact Puiseux coefficients from arbitrary Cauchy coefficients are not uniformly computable | Section 15 | Human-complete synthesis of repository reduction | Retained barrier |
| B5 | Metastability does not yield a computable Cauchy modulus | Section 15 | Human-complete Specker-style reduction | Retained barrier |
| E1 | `pra_iff_native` transports a supplied completed iPRA derivation | Pinned backend | Backend-checked | `ConciseIPRA.NativeBiInterpretation` |
| O1 | General Faltings/Siegel height producer | Sections 11–12 | Conditional/open | Uniform verifier isolated |
| O2 | General rational covering representatives for Mordell–Weil descent | Section 12 | Conditional/open | Relational verifier isolated |
| O3 | Generic `Prf PRAAx` compiler implemented and built in Lean | Section 13 | Lean-blueprint; open engineering task | Visible `sorry` in blueprint |
