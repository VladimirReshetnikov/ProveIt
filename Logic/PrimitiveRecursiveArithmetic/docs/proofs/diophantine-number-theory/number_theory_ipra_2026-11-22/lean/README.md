# Lean blueprint: status and replay plan

**Status: uncompiled. No new kernel-checked theorem is claimed.**

This directory gives concrete numerical definitions and outstanding correctness goals. It also provides example sentences in the actual ProveIt object language. The human arguments are in the companion PDF and LaTeX chapters.

## Layers of the intended formalization

1. **Semantic algorithms.** Define functions on Lean natural numbers, integers, lists, and rational numbers. Establish the mathematical specifications stated in the report.
2. **Primitive recursive codes.** Construct fixed `PR` syntax trees for these functions; prove the defining equations and their agreement with the semantic definitions. Encode rationals by signed numerators and positive denominators, and encode lists with the chosen finite list representation.
3. **Object-theory proofs.** Construct proof terms whose conclusions are the translated first-order sentences and whose object-theory axioms are exactly `PRAAx`. Compile bounded predicates through `BFm` and Boolean reflection, and use quantifier-free induction for the loop invariants.

The first layer is not a substitute for the third. Records with names such as `AnalyticGoals`, `QuadraticGoals`, or `RequiredDerivations` enumerate proof obligations; defining the record does not prove any of its fields.

## Files

| File | Role |
| --- | --- |
| `ElementaryDefinitions.lean` | Bounded arithmetic algorithms, arithmetic functions, congruences, finite CRT, and elementary specifications |
| `ElementaryBlueprint.md` | Porting route for the elementary chapter |
| `QuadraticDefinitions.lean` | Residue and root searches, Legendre symbols, primitive roots, and square-representation goals |
| `DiophantineTargets.lean` | Rational, continued-fraction, approximation, Pell-bound, and Diophantine interfaces |
| `diophantine_blueprint.md` | Detailed witness bounds and proof obligations for the Diophantine chapter |
| `AnalyticDefinitions.lean` | Finite prime, sieve, harmonic, zeta, Euler-product, and divisor-mean specifications |
| `AlgebraicDefinitions.lean` | Quadratic integer pairs, capped valuations, Hensel digits and compatible lifts, finite partition predicates |
| `TranscendenceDefinitions.lean` | Liouville rational truncations and explicit polynomial-separation construction |
| `ProveItTargets.lean` | Exact object-language four-square and Pell sentences and a wrapper for the existing bounded-reflection derivation |

The report defines the remaining mathematical predicates and invariants in detail. `theorem_inventory.json` in the parent directory identifies every numbered result and its source chapter. No use of `sorry` or a newly postulated theorem is intended to discharge any of these outstanding obligations.

## Standalone semantic replay

The toolchain and dependency are pinned to match the inspected ProveIt environment:

```text
Lean:    leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
```

With that toolchain installed and network access to the dependencies, the proposed starting commands from this directory are:

```sh
lake update
lake build
```

These commands were **not run** during preparation. The first replay may expose API or elaboration issues that require repair. Successful compilation of the definitions and goal records would still not discharge the goal fields.

`ProveItTargets.lean` is deliberately excluded from the standalone library roots because its imports belong to the external ProveIt checkout.

## Object-level integration

Use ProveIt at commit `bbb85238dac533fc4b7b84a750cca864fe35fed5`. Its relevant project directory is:

```text
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/
```

Bring `ProveItTargets.lean` into an isolated checkout of that project or configure a downstream Lake project to expose the same imports. Replay it with the pinned toolchain and project dependencies. Its small reflection wrapper reuses `Foundations.BoundedSyntax.boolean_reflection_closed`; the number-theoretic fields remain unimplemented requirements.

The concrete sequence of proof work is given in the PDF's formalization chapter: shared encodings and Boolean compilation; fixed-clock invariants; elementary arithmetic and finite permutations; norm identities and square descents; Pell approximation and collision; finite analytic inequalities; Hensel and partition transformations; then closed endpoint assembly and dependency audit.

Two interface details are especially important:

- `Core.Search` searches for **zero**, while the report's predicates use **one for truth**. Pass the complemented truth bit when reusing its search theorem.
- `PellGeneral` starts from a supplied norm-one unit. The explicit bounded existence proof in this report must be implemented before that interface can supply the intended classification.

Finally inspect each exact endpoint type and its complete dependency closure. A clean `#print axioms` for an ordinary Lean theorem is insufficient unless the theorem actually provides the intended object derivation under `PRAAx`.
