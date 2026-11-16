# Theorem and claim ledger

Status vocabulary:

- **Human-complete**: the report gives a complete mathematical argument.
- **Python-tested**: exact finite instances are checked by the included tests.
- **Lean-outline**: definitions, theorem signatures, and a dependency-ordered
  completion path are supplied, but the file was not compiled.
- **Backend-checked**: inherited from the pinned `ConciseIPRA` library.
- **Conditional**: a theorem is complete once the named quantitative producer
  is supplied.
- **Barrier**: the unrestricted strengthening is shown to be unavailable in
  the intended effective/constructive setting.

| ID | Claim | Status | Artifact |
|---|---|---|---|
| F1 | Every fixed bounded formula has a PR Boolean characteristic function and an iPRA reflection proof. | Human-complete; Lean-outline | report Section 6; `lean/BoundedFormulaCompiler.lean` |
| F2 | Fixed-precision query-table induction keeps the induction predicate quantifier-free. | Human-complete | report Section 7 |
| F3 | Finite-trace reflection constructs a global iPRA proof from base, step, and final `Prf PRAAx` proofs. | Human-complete; Lean-outline | report Section 8; `lean/ObjectTraceCompiler.lean` |
| F4 | Run-zero and run-successor equations are instances of upstream `PRA.precZero` and `PRA.precSucc`. | Source-level Lean proof; not compiled here | `lean/ObjectTraceCompiler.lean` |
| F5 | Reverse demand propagation on a finite contract DAG is sound and compositional. | Human-complete; Python-tested | report Section 9; `code/finitary_kernel.py` |
| F6 | Certified DAG composition produces one bounded global trace and one qf invariant. | Human-complete; Lean-outline | report Section 9; `lean/CertifiedProgram.lean` |
| F7 | Backward viability is equivalent to existence of a full finite compatible path. | Human-complete; Python-tested; Lean-outline | report Section 10 |
| F8 | Least viable successor gives finite dependent choice without an infinite-choice principle. | Human-complete; Python-tested | report Section 10 |
| F9 | Stable quotient erasure makes the final observable independent of finite tie-breaking. | Human-complete; Python-tested | report Section 10 |
| F10 | A diameter modulus plus a summable motion budget turns changing-horizon viable paths into a regular name. | Human-complete; Lean-outline | report Section 11 |
| F11 | Guarded reciprocal is uniformly correct under a positive rational apartness margin. | Human-complete; Python-tested | report Section 11 |
| F12 | Three-way guards avoid discontinuous exact branching and refine monotonically. | Human-complete; Python-tested | report Section 11 |
| F13 | Finite-net minimization is PR and transfers through an explicit modulus. | Human-complete; Python-tested | report Section 12 |
| F14 | A height bound gives a complete finite list for any decidable coded-point predicate. | Human-complete; Python-tested; Lean target | report Section 14 |
| F15 | A certified complete finite list gives a height bound by finite maximum. | Human-complete; Python-tested; Lean target | report Section 14 |
| F16 | Exact rational bisection produces a regular name for the inverse of `y^3+y`. | Human-complete; Python-tested; Lean target | report Section 14; example JSON |
| F17 | A strong finite simplicial carrier yields a choice-independent induced homology map. | Human-complete at finite-chain level; Lean target | report Section 14 |
| F18 | Guarded finite affine gluing is reducible to bounded ring equations and certified cover data. | Human-complete framework theorem; conditional application | report Section 14 |
| B1 | No total PR universal evaluator exists. | Barrier | report Section 17 |
| B2 | Finiteness/cardinality alone does not uniformly produce a search cutoff. | Barrier | report Section 17 |
| B3 | Exact sign/side selection from arbitrary real names is not constructively uniform. | Barrier | report Section 17 |
| B4 | Metastability alone does not uniformly yield a Cauchy modulus. | Barrier | report Section 17 |
| E1 | A completed `Prf PRAAx` proof transports to the native scalar core by `pra_iff_native`. | Backend-checked | upstream `NativeBiInterpretation.lean` |
| O1 | Kernel-check the generic trace compiler. | Open engineering milestone | `lean/LEAN_PLAN.md` |
| O2 | General Faltings/Siegel height producers. | Conditional/open mathematics | report Section 17 |
| O3 | Uniform rational covering representatives for general Mordell-Weil descent. | Conditional/open mathematics | report Section 17 |
| O4 | Effective constants for all targeted prime-distribution packets. | Conditional/open mathematics | report Section 17 |
