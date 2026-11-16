# KIFC formalization plan

## Upstream

Pin ProveIt commit `8649990597d73657bde480b6c389de7f85bc0cb0`
or explicitly re-audit a later commit. Add this artifact's `lean/KIFC` directory
under `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/KIFC`
and adjust import prefixes accordingly.

## Phase 0: compile the kernel core

1. Compile `KernelCore.lean` against `IPRADerivations.Core.Basic`.
2. Resolve only API/notation differences; do not weaken theorem conclusions.
3. Run `#print axioms` for `Schedule.compile` and `LoopCertificate.compile`.
4. Compile the two-square adapter in `Examples.lean`.

Exit criterion: no `sorry`; public conclusions are `Prf PRAAx` values.

## Phase 1: Boolean object library

Implement PR symbols and object proofs for Boolean not/and/or, zero test,
equality, `<`, `<=`, maximum, conditional selection, pairing projections, and
fixed-radix table access. Prove Boolean range and reflection.

Do not build an object-level formula evaluator. A metalevel constructor should
return a specialized `Reflected n` value for one fixed formula.

## Phase 2: bounded folds

For a fixed predicate symbol, generate `allB` and `anyB` by `PR.prec`. Prove
zero/successor equations at arbitrary terms, Boolean range, and reflection of
bounded universal/existential formulas. Keep the actual induction invariant an
equality between fold terms.

## Phase 3: least bounded search

Generate the `(found,witness)` recurrence. Prove the QF invariant listed in
`SearchBlueprint.lean`. Export foundness, validity, and minimality. Test on least
divisor, bounded table lookup, and guarded argmin.

## Phase 4: state/table coding and generic trace

Choose one fixed tuple/table code. Derive constructor/projection equations.
Build a generic trace symbol and instantiate `LoopCertificate` for a generated
state invariant.

## Phase 5: finite relational viability

Use rectangular rows of width `max B_i`. Compute viability backward by forward
recursion on reverse time. Prove the row recurrence, a bounded tuple path
checker, viability iff suffix-checker acceptance, and least viable path
validity.

## Phase 6: metric observers

Reuse signed integer/rational codes from `IPRADerivations.Core.Integers`.
Derive order, absolute difference, triangle inequality, finite sum
monotonicity, exact observer elimination, diameter observer elimination, and
the shrinking-cloud tail theorem.

## Phase 7: generated deterministic example

Generate a complete theorem module for exact rational bisection of
`y^3+y=x`:

1. algebraic monotonicity identity;
2. initial bracket;
3. packed bisection loop;
4. QF bracket/width invariant;
5. terminal interval theorem;
6. closed theorem and native transfer;
7. axiom audit.

## Phase 8: generated relational example

Use a Cauchy input for `x`, allow both child intervals when sign is uncertain,
compute finite viability, and export a diameter-stable midpoint observation.

## Phase 9: graph elaborator

Only after phases 7 and 8 compile, implement a typed metalevel graph AST and a
generator that emits specialized PR syntax, local rules, a loop certificate,
and a `Schedule`. The object theory must not evaluate graph codes.

## Completion gates

A theorem is complete only when:

- its object formula is explicit;
- the public theorem has type `Prf PRAAx`;
- no `sorry` or theorem-specific axiom occurs;
- `#print axioms` is recorded;
- a clean build from the pinned commit passes;
- native transfer is applied after the ordinary derivation.
