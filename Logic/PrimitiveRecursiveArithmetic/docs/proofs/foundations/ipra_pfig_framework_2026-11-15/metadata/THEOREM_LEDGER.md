# Theorem and claim ledger

Status vocabulary:

- **Human-complete**: a complete mathematical argument is supplied in the paper.
- **Finite-tested**: exact finite instances or properties are exercised by the Python suite.
- **Inherited object theorem**: an inspected ProveIt source file concludes an actual `Prf PRAAx` derivation; this artifact did not recompile it.
- **Lean blueprint**: definitions and theorem signatures are supplied, but the target is not kernel-checked here.
- **Conditional/open**: the generic verifier is described, while a named quantitative producer remains.

| ID | Claim | Paper | Status | Artifact |
|---|---|---|---|---|
| P1 | Structural Booleanization of every fixed bounded formula | Sec. 4 | Human-complete; Lean blueprint | `PFIG/BooleanBlueprint.lean` |
| P2 | Least bounded search, soundness, and minimality | Sec. 4 | Human-complete; finite-tested; Lean blueprint | Python search tests |
| P3 | Object trace invariant for PR state recursion | Sec. 5 | Human proof; inherited object theorem | `ObjectLoopBlueprint.lean` migration target |
| P4 | Reflection of finite trace certificates | Sec. 5 | Human-complete; Lean blueprint | paper + plan |
| P5 | Primitive-recursive reverse demand and minimality | Sec. 6 | Human-complete; finite-tested; Lean blueprint | `DemandGraph` tests |
| P6 | PFIG normal form: fixed graph to encoded bounded loop | Sec. 3 | Human-complete construction; Lean blueprint | `GraphBlueprint.lean` |
| P7 | Two-pass PFIG soundness | Sec. 6 | Human-complete from local object certificates; Lean blueprint | `Compiled.sound` plus open compiler target |
| P8 | Viability iff compatible finite path | Sec. 7 | Human-complete; finite-tested | exhaustive/random tests |
| P9 | Least viable path and finite dependent choice | Sec. 7 | Human-complete; finite-tested; Lean blueprint | `FiniteRelationTower` |
| P10 | Adjacent coherence from viable-cloud diameter and edge motion | Sec. 8 | Human-complete; finite-tested | shrinking-cloud test |
| P11 | Regular name from summable motion budget | Sec. 8 | Human-complete; Lean blueprint | relation blueprint |
| P12 | Stable-observer erasure | Sec. 8 | Human proof; inherited object combinator; finite-tested | `ExactCore.lean`, Python test |
| P13 | Guarded branch stabilization under a positive gap | Sec. 9 | Human-complete; finite-tested; Lean blueprint | `guarded_argmin` |
| P14 | Precision-contract composition | Sec. 9 | Human-complete; exact case source-complete uncompiled | `ExactCore.lean` |
| P15 | Certified finite-cover gluing | Sec. 10 | Human-complete; Lean blueprint | `ApplicationsBlueprint.lean` |
| P16 | Height bound implies complete finite list | Sec. 10 | Human-complete; finite-tested; Lean blueprint | `HeightEnumeration` test |
| P17 | Complete finite list implies height bound | Sec. 10 | Human-complete; finite-tested; Lean blueprint | `HeightEnumeration` test |
| P18 | Equality stability and stability of all negative translations | Sec. 11 | Human-complete; Lean blueprint | negative-transfer blueprint |
| P19 | Translation of ClassicalPRAAx derivations to iPRA | Sec. 11 | Human-complete; Lean blueprint | negative-transfer blueprint |
| P20 | Retained equivalence and retained transfer | Sec. 11 | Human-complete; Lean blueprint | negative-transfer blueprint |
| B1 | No total PR universal evaluator | Sec. 13 | Human-complete diagonal barrier | paper |
| B2 | No unrestricted exact sign/axis selector | Sec. 13 | Constructive discontinuity barrier | paper |
| B3 | Metastability does not uniformly yield a Cauchy modulus | Sec. 13 | Computability barrier | paper |
| B4 | Finiteness/cardinality does not yield a search cutoff | Sec. 13 | Halting-style barrier | paper |
| B5 | Exact branch data from arbitrary Cauchy input is not uniformly available | Sec. 13 | Discontinuity/exact-zero barrier | paper |
| O1 | Shared object Booleanization compiler | Sec. 14 | Open engineering task | `BooleanBlueprint.lean` |
| O2 | Generic object viability-table reflection | Sec. 14 | Open engineering task | `RelationBlueprint.lean` |
| O3 | Verified internal PFIG AST compiler | Sec. 14 | Open engineering task; generated specialization is interim route | `GraphBlueprint.lean` |
| O4 | General effective Faltings/Siegel height producer | Sec. 10, 13 | Conditional/open mathematical producer | isolated interface |
| O5 | Uniform rational representatives in general Mordell-Weil descent | Sec. 12, 13 | Conditional/open mathematical producer | isolated interface |
