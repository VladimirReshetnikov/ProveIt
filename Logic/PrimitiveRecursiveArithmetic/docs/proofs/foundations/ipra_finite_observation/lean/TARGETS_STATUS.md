# Status of Targets.lean

`Targets.lean` imports only `Std` and **type-checks under Lean 4.32.0**.
It contains executable definitions and explicit semantic specifications.
It contains no completed proof of the analytic or algebraic theorems below.
The `Spec` structures have proof-valued fields that a future implementation
must fill, and the `Goal` definitions name propositions still to be proved.

The file gives concrete definitions for:

- rational regular samplers, equality and order of names;
- finite rational points, the cube, and its maximum-coordinate distance;
- finite-net infimum and coherent-minimizer specifications;
- the midpoint strong-convexity condition;
- quantitative positivity and a finite reading schedule for multiplicative
  convexity;
- the endpoint Lipschitz bound and the explicit derived local modulus;
- rational polynomials, degree, evaluation, affine points, feature vectors,
  the superelliptic section bound, and the supplied-cover implication;
- Gaussian rational polynomials and coefficient norms;
- finite coefficient contracts, name factorization targets, the root query
  and deflation verification schedules, and the full local deflation target.

Two deliberate conventions are useful when comparing the file with the
paper. The infimum sampler is the midpoint of the nested intervals. Its
current grid minimizer is bounded using the running lower endpoint plus
the error allowance; it is not incorrectly asserted to realize the running
upper endpoint. The generic point-name evaluator uses a shift of three
instead of two, accommodating the two-error regular-name convention.

## What successful compilation means

Compilation verifies that the definitions, interfaces, and target
propositions are well typed. It does **not** establish that a `Spec` is
inhabited or that a `Goal` holds. In particular, an ambient Lean function
field is not a certificate of primitive-recursive definability.

To complete the iPRA formalization, implement the finite algorithms, prove
their semantic finite contracts, construct their particular PR syntax,
prove Boolean reflection for the bounded predicates, and construct the
actual object-language derivations. The fixed-program schema boundary
must be retained during that translation.

The separately compiled `FiniteObservation.lean` file contains proved
generic finite lemmas. Its status should not be confused with the
specification-only status of this file.

## Reproduce the type check

From this directory with the pinned toolchain:

```sh
lean Targets.lean
```

Observed command in this environment:

```text
/workspace/scratch/71838c83a0ea/toolchain/lean-4.32.0-linux/bin/lean Targets.lean
```

Exit status: `0`. Standard output and standard error were empty.
