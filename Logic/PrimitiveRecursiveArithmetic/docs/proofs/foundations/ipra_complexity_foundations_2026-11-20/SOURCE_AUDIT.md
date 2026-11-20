# Source audit

Repository: `VladimirReshetnikov/ProveIt`.

Pinned commit: `83421593771f877bc1ae98f4229eb35507bff05b`.

Inspected on 20 November 2026 through the GitHub connector. The upstream project was not rebuilt in this task. The standalone Lean companion has no upstream repository imports.

## Inspected source files

- [Logic/PrimitiveRecursiveArithmetic/README.md](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/README.md)
  Git blob: `a998cff2fb389272cfe1052eeedb0f2a6b826198`.
- [Logic/PrimitiveRecursiveArithmetic/DEPENDENCIES.md](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/DEPENDENCIES.md)
  Git blob: `eda2eddf41050ba3bc1e9c133e59405c1a7fd3e0`.
- [Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean)
  Git blob: `3251631592070d9ed3687cc0bf7dbd5eb452e46f`.
- [Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean)
  Git blob: `a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348`.
- [Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean)
  Git blob: `0969040f77fdd3ed9526e360e7a998584b4d9d8c`.
- [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/BoundedFormulas.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/BoundedFormulas.lean)
  Git blob: `33711f322d09dcf8ef81b0dd2c7aac187875f9d6`.
- [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/LeastBoundedWitness.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/LeastBoundedWitness.lean)
  Git blob: `2243e035077bdabf5f8b2f1e751a7ae6753703d9`.
- [Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/BoundedSyntaxInduction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/BoundedSyntaxInduction.lean)
  Git blob: `70864657cc5fc08610654ab4e92da96508eff7c4`.
- [lean-toolchain](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/lean-toolchain)
  Git blob: `94b9f495baff80fd9cb44aad8f4762cb3b2066fe`.
- [LICENSE](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/LICENSE)
  Git blob: `9ba84db3ce7197b149cadca52befe271bda64d8b`.

## Reuse decisions

- Use the repository definition of first-order iPRA and its ordinary `Prf PRAAx` target.
- Plan to reuse the existing bounded-formula reflection, least-witness and bounded-induction endpoints. Their concrete source was inspected; this package does not assert that the new main proofs already inhabit those endpoints.
- Keep the checked standalone semantic core separate from the object-language compiler obligations.
- Treat source inventory and packet summaries as provenance, not as verification of every packet.
- The pinned repository toolchain is Lean 4.32.0; the independent companion was tested with Lean 4.19.0 and bundled Std. Integration is a separate, explicit porting/build milestone.

## External mathematical sources

The report bibliography records primary papers by Cook, Savitch and Immerman, the author-hosted description of Buss's intuitionistic bounded arithmetic, official Lean documentation, and the Clay Institute's P versus NP status. The Wikipedia article supplied the requested topic map. All detailed iPRA constructions, induction audits, proof boundaries and explicit diagonal presentation are developed within the report; none is asserted to be a pre-existing complete iPRA formalization in those sources.

The Savitch publisher abstract was available, but its full publisher page returned an access error. The report therefore provides the finite proof independently and does not claim to have inspected that full paper.
