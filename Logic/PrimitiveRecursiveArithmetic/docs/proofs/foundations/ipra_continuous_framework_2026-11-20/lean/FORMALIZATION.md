# Formalization boundary and completion plan

All four `.lean` files are **uncompiled** in this delivery environment.
There was no Lean executable available. The report is the human proof; the
sources are the requested outline and a concrete specification of remaining
work, not completed proofs of the analytic main theorems.

## Files and obligations

### ObjectContracts.lean

Imports the actual `ConciseIPRA.PR` API inspected at upstream commit
`5f3be02388442f16487d2dc5c2529961dd783d2b`.

- `CompiledContract` stores an actual `Prf PRAAx` proof.
- `specialize` uses `Prf.subst`.
- `discharge` and `closed` use `Prf.trans`.
- `contract_compose` uses the existing intuitionistic implication composition.

These structural adapters do not establish any new continuous theorem.

### RelationalNamesBlueprint.lean

Defines a deterministic trace interface, totality, regular names, approximate
equality, arithmetic code-constructor contracts, joint totality and diagonal
completion, batch totality and clock obligations. Fixed-call composition is
demonstrated logically. To complete the object formalization:

1. Instantiate a genuine fixed PR machine-step definition and its finite runner.
2. Construct code compilers plus forward/backward trace maps.
3. Prove their correctness by QF induction over explicit traces.
4. Implement rational slack removal and name equivalence.
5. Derive addition, product and completion contracts by finite witness wiring.
6. Keep batch/iteration totality explicit where the number of calls varies.

An arbitrary Lean function in a field of `TraceKernel` does not prove that the
function is PR. The bridge must replace it by the actual `PR` syntax.

### CategoryModelBlueprint.lean

Defines the rational core, regularity, name equivalence, completion diagonal,
core maps, extension, finite nets, atomic predicates, formula syntax,
well-formedness, evaluator and W/C weights. To complete:

1. Derive regularity and extensionality of the extension in encoded rationals.
2. Implement the bounded formula/environment table and PR well-formedness test.
3. Prove argmin/argmax perturbation using certified net selectors.
4. Booleanize the bounded pair-table invariant and apply QF induction.
5. Export the cross-precision comparison as `Prf PRAAx`.
6. Prove semantic adequacy separately and formalize relational/many-sort adapters.

Uniform syntax uses one fixed finite primitive signature. Variable codes for
arbitrary atomic evaluators need explicit clocks or successful evaluation batches.

### AnalyticBlueprint.lean

Defines rational vector norm, field contracts, Euler nodes/polygons, the
Gronwall budget, name targets, Gaussian rationals, segment clearance and the
finite kernel identity target. To complete:

1. Use `PR` code definitions for vectors, rational steps and bounded logs.
2. Prove the tube invariant for actual Euler states.
3. Construct the common refinement and derive the actual error recurrence.
4. Instantiate `DiscreteGronwall.gronwall_three` with positive denominators.
5. Prove the explicit N/p budget and export polygon regularity.
6. Define integral names and prove common-refinement/linearity/stability.
7. Assemble the integral equation and difference-quotient observations.
8. Finish the original-name uniqueness adapter with the displayed N/p schedule.
9. Prove exact segment-minimum correctness, guarded reciprocal laws, kernel
   identity, quadrature and Taylor/derivative remainder bounds.

## Existing modules to reuse

The audit identifies actual upstream modules for `SetoidInterpretation`,
`PresentedCategory`, `Yoneda`, `DyadicNames`, `CoherentTower`,
`BoundedSyntax`, `FiniteQueryDemand`, `FiniteQueryTable`, `NetTransfer`,
`FiniteGluing`, `GuardedTotalization`, `DiscreteGronwall`, `OdeRefinement`,
`OdeUniqueness`, rational arithmetic and Gaussian-rational arithmetic.

Reuse means importing the precise theorem and supplying all its premises.
The source audit does not certify that every suggested module name has the
exact convenience wrapper a later implementation may prefer.

## Acceptance criteria

- Actual fixed PR definitions, with all denominator and domain guards.
- Actual formulas `Fm PTm n`, not only host statements about Lean reals.
- Closed or explicitly conditional `Prf PRAAx` endpoints for the new claims.
- No implicit induction on unbounded totality or coherence formulas.
- No suppressed evaluator, net, batch, margin or overlap hypotheses.
- Successful Lean elaboration and the upstream axiom audit.
- A separate semantic theorem identifying the arithmetic names with the
  intended mathematical objects.

No full upstream dependency closure is copied into this archive. The pinned
repository is the declared build dependency for object proof adapters. The
Python reference programs and report sources are self-contained.
