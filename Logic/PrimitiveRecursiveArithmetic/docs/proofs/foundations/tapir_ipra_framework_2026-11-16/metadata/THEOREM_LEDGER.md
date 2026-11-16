# Theorem ledger

| ID | Result | Dependencies | Status |
|---|---|---|---|
| T1 | Plan soundness: `Plan Γ φ -> Γ ⊢[PRAAx] φ` | checked `Prf` rules, `PRA.qfInd` | full human proof; no-placeholder Lean candidate; unelaborated |
| T2 | Schedule compilation: every output of `Schedule R outs` has a plan from `R` | T1, `Prf.trans`, list membership | full human proof; no-placeholder Lean candidate; unelaborated |
| T3 | Residual closure | checked `Prf.trans` | inherited immediate corollary |
| T4 | Syntactic residual exactness after backward slicing | finite graph algorithm | human proof; Python tests |
| T5 | Certificate sealing | checked `Prf.exE` | inherited immediate corollary |
| T6 | Exact observer erasure | T5, equality substitution | human proof schema; Lean blueprint |
| T7 | Stable observer erasure | finite triangle/telescoping inequalities | human proof schema; Lean blueprint |
| T8 | Named bounded witness | checked `BoundedReflection.bounded_choice` | checked upstream wrapper |
| T9 | Arity-polymorphic least-search specification | checked one-parameter proof pattern, `recDef`, qf induction | full human proof; Lean blueprint |
| T10 | Arity-polymorphic bounded reflection | T9, bounded product/complement | full human proof; Lean blueprint |
| T11 | Static bounded-formula compilation | T10, propositional bit combinators | structural human proof; Lean blueprint |
| T12 | Clocked trace reflection | checked `PRA.qfInd` / `IPRA.ind` | reduction to checked theorem |
| T13 | Conditional complete-list theorem | T10, supplied height/code bound | full human proof schema; Lean target |
| T14 | Finite relational composition via viability | T10, bounded recursion | full human proof schema; reference tests |

No row marked human proof or source candidate is represented as a new
kernel-checked theorem.
