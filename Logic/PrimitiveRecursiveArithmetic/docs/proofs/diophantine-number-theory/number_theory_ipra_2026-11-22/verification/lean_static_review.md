# Static review of the Lean outline

**Status:** Manual source and mathematical-interface review only. No Lean compiler or Lake executable was available, and this review does not claim successful parsing, elaboration, compilation, kernel checking, or completed proofs.

Reviewed all seven `.lean` files, both Markdown blueprints, `lean-toolchain`, and `lakefile.toml`. Parsed the TOML independently and verified that its six distinct module roots correspond to existing source files. The Lean and Mathlib pins agree with `provenance.json`.

## Corrections made

1. In `AnalyticDefinitions.lean`, made the natural-to-integer conversion in the Möbius sieve sum explicit: `mobius d * ((x / d : Nat) : Int)`. This avoids reliance on mixed-arithmetic coercion inference and leaves the mathematical expression unchanged.
2. In `DiophantineTargets.lean`, added the explicit nonzero leading-coefficient hypothesis to `RationalRootSpec`. Its declared degree now matches the actual-degree hypothesis of the human theorem. The hypothesis is input data, not a desired conclusion.
3. In `lakefile.toml`, documented that the default target contains only the standalone semantic outlines. `ProveItTargets.lean` must be checked separately in the pinned ProveIt project; its external object-calculus dependencies are not included in this standalone package. Compiling the semantic definitions would not prove the goal-record fields.

## Goal-record audit

`AnalyticGoals`, `AlgebraicGoals`, `QuadraticGoals`, and `TranscendenceGoals` are proposition-valued records listing proof obligations. No inhabitant, global instance, axiom, or theorem asserting these records is supplied. `RequiredDerivations` likewise records missing object-language derivations. The existing bounded-reflection wrapper in `ProveItTargets.lean` matches the signature of the inspected repository theorem `boolean_reflection_closed`; that wrapper is still uncompiled here.

The Pell guard in the object target remains a parameterized primitive recursive code. Its construction and reflection as the intended nonsquare predicate are explicit completion requirements; choosing a false guard would not satisfy those requirements. Fundamental Pell classification assumes a minimal nontrivial unit, as does the human classification theorem; existence and bounded recovery are separate obligations.

## New numerical definitions

The quadratic four-square search uses a complete finite box with digits in `0..n`; its failure default is not treated as proof that a representation exists. The two-square criterion is the explicitly decidable prime-exponent condition, not an assumed representation. Legendre-symbol and reciprocity goals have the required primality, oddness, and distinct-prime hypotheses.

For transcendence, trailing-zero removal determines the actual degree. The coefficient sum remains unchanged by trailing zeros. The partial sum starts at factorial index one and agrees with the report. The search scans exactly degree-plus-one distinct truncation indices. Its fallback is not asserted correct independently; proving success is part of the polynomial-separation obligation. The positive margin matches the report's degree, coefficient, and factorial bounds, including the nonzero constant-polynomial case.

No obvious remaining definition or goal-framing inconsistency was identified. Compiler-dependent syntax and type elaboration still require an actual build in the pinned environment.
