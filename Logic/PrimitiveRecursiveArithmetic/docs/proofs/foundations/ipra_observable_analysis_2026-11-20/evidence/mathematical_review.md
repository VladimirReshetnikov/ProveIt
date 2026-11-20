# Mathematical and integration review

The manuscript was checked in parallel by contributors responsible for the measure, analytic/categorical, and Lean/model-theoretic parts. This is an internal consistency review, not independent peer review.

## Corrections incorporated

- The represented PR part of a completion is explicitly distinguished from the full external completion. No universal PR evaluator is asserted.
- The represented distance, index shifts, diagonal construction, and extension constants are explicit. The symmetric and one-sided regularity conventions are related by an index shift.
- Majorant-tail extraction is separated from the convergence-in-measure cutoff. No rate is obtained from bare pointwise convergence. Positivity of the measure threshold is retained in the external adequacy argument.
- Multiplier claims require a supplied uniformly bounded, sup-Cauchy multiplier; they do not extend multiplication to all of L1.
- Probability transport has a bounded exact baseline. Its efficient certificate checks feasible primal and dual data; it does not assert a polynomial bound for forest enumeration or silently invoke an optimization oracle.
- The normed algebra includes scalar compatibility. Power-series tail, derivative-tail, and quadratic-remainder bounds use the correct intermediate radius. Noncommutative derivatives use ordered insertions.
- General inverse construction requires both residual gaps. The one-sided shift example explains the necessity.
- Homotopy repair requires an exact square-zero differential and a certified positive norm margin. It does not assume h squared is zero or h commutes with the defect. The matrix example was checked against the exact script.
- The reverse-weight producer requires strictly lower-triangular nonnegative data. The dual verifier can accept cyclic inequalities only after those inequalities have been justified independently.
- Runtime efficiency claims are algebraic operation counts per sink-weight vector, not polynomial bit-complexity statements.
- The final proof-status ledger was compared with the manuscript and compiled Lean project. All 15 claim anchors resolve. Analytic human proofs, checked host-Lean kernels, and remaining object-iPRA derivations are separated.

## Evidence and remaining boundary

The exact-rational example programs passed, and their source hashes are recorded in integration_checks.json. The Lean source hashes and actual axiom dependencies are in ../lean/verification.json, with the compiler output in ../lean/build.log. Standard rational-arithmetic dependencies include Classical.choice and are not presented as intuitionistic object proofs.

The intended integration reuses ProveIt's existing BoundedSyntax, RealizerGraph, and RealizerMasterInterface. It does not replace them with a second calculus or relabel host propositions as embedded Prf PRAAx values. No new main analytic theorem has yet been compiled into that embedded judgment.

The source review was selective and pinned, not a rebuild or complete audit of ProveIt. Bibliographic attribution identifies established completion, integration, transport, continuous-model, and perturbation methods. The report claims reusable constructions and explicit arithmetic refinements rather than priority for those underlying mathematical theorems.
