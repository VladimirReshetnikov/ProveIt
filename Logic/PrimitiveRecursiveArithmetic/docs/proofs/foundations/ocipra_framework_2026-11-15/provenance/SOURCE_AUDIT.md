# Source audit

## Pinned baseline

- Repository: `VladimirReshetnikov/ProveIt`
- Commit: `9df5cbdf39e6220be823f611987bd584d37711fd`
- Commit time reported by GitHub: 2026-11-16 05:24:07 UTC
- Audited subtree: `Logic/PrimitiveRecursiveArithmetic`

## Primary files read

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
- `.../PR.lean`
- `.../Deduction.lean`
- `.../Native.lean`
- `.../NativeBiInterpretation.lean`

The current directory README reports 72 research packets, six packets with
framework/small-example `Prf PRAAx` constructions, and no packet whose main
application theorem has that endpoint.

## Foundation packets compared

- `foundations/ipra_framework`
- `foundations/ipra_unified_finitary_framework_2026-11-15`
- `foundations/ipra_finite_use_framework_2026-11-15_v2`
- `foundations/ipra_cfp_contract_compiler_2026-11-15`
- `foundations/ipra_resources_and_elimination_2026-11-15`
- `foundations/ipra_coherent_methods_2026-11-15`
- `foundations/ipra_local_global`
- `foundations/ipra_presentations_to_witnesses`
- `foundations/ipra_embedding_framework_2026-11-15`
- `algebra/ipra_stable_observables`

## Reused ideas, explicitly credited

The report treats finite observations, proof-producing traces, backward demand,
relational clouds, stable observables, height/list separation, and the current
ConciseIPRA bridge as prior repository infrastructure.  Its additions are:

1. a single typed statement calculus covering deterministic, relational,
   stable-observable, and conditional-producer theorems;
2. a dual `NPrf`/`Prf PRAAx` backend that avoids universal evaluation;
3. a finite monotone demand-closure theorem for cyclic demand specifications;
4. a uniform admissibility test and packet-conversion workflow;
5. a consolidated proof showing exactly where local object derivations enter
   the global compiler.

## Scope boundary

No repository files were modified.  Existing packet claims were read as
reported claims, not independently recompiled.  The supplied Python tests check
only the new finite reference algorithms.  The Lean outline was not compiled
because Lean was unavailable in the artifact runtime.
