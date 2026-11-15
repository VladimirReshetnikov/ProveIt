# Lean formalization outline

`Blueprint.lean` is a **documentation-only, unfinished formalization plan**. All proposed declarations are inside a block comment. It contains no claimed formal proof, no admitted theorem, and no stand-in axiom. It was **not compiled**; Lean was unavailable in the execution environment.

The exact finite target is: for a rational table `F : {0,...,N}^d -> Q^m`, with `N >= 1` and `delta > 0`, if every pair of vertices on opposite coordinate faces has image distance at least `delta`, while every standard Kuhn simplex has image diameter strictly below `delta/d`, then `d <= m`. The zero-dimensional case is treated separately. The proof uses cubical Sperner parity, staggered rational cells, and a finite injection from source coordinates to target coordinates.

## What must be formalized

1. Explicit Kuhn simplex and face enumeration, including the interior-face pairing involution.
2. Cubical Sperner parity with labels `0,...,d`: on lower coordinate face `i`, the label is at most `i`; on the upper face `i`, it differs from `i` (zero-based coordinates).
3. Shifted-cell floor arithmetic, the first-zero coloring, and rational threshold separation.
4. Natural-number codes and fixed primitive-recursive definitions for all bounded scans.
5. An **object-language derivation** in `ConciseIPRA.Prf PRAAx`, followed by transfer to `NPrf`.
6. The quantitative map-to-finite-table wrapper with explicit moduli and error margins.

The blueprint gives the detailed lemma sequence. Its crucial induction audit fixes the full labeling table and proves parity for its nested lower-face restrictions. The invariant is an equation between finite primitive-recursive scans, so it fits quantifier-free induction. Induction on an unbounded statement about all labelings is not substituted for this step.

## Verified upstream integration points

Inspected ProveIt commit: **`daade0300022828cdba33a324d987997fee9fa08`**. Root configuration pins **Lean and mathlib `v4.32.0`**.

All files below are in `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`:

| File | Existing interface |
| --- | --- |
| `PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd` |
| `Deduction.lean` | Intuitionistic first-order derivability `Prf`; notation `Gamma ⊢[PRAAx] phi` |
| `TeqReflect.lean` | Characteristic terms for quantifier-free formulas; `chi_iff`; `Teq.qfInd` |
| `TeqPair.lean`, `TeqRec.lean` | Pairing and compilation of primitive recursion through a scalar iterator |
| `NativeBiInterpretation.lean` | `pra_iff_native`, `native_iff_pra`, and both round trips |

Namespace: `LeanProofs.ConciseIPRA`.

Pinned source links:

- [PR.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/daade0300022828cdba33a324d987997fee9fa08/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean)
- [Deduction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/daade0300022828cdba33a324d987997fee9fa08/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean)
- [NativeBiInterpretation.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/daade0300022828cdba33a324d987997fee9fa08/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean)
- [ConciseIPRA README](https://github.com/VladimirReshetnikov/ProveIt/blob/daade0300022828cdba33a324d987997fee9fa08/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md)

The intended endpoint is a concrete closed formula `finiteDimensionFormula : Fm PTm 0` and a proof of `[] ⊢[PRAAx] finiteDimensionFormula`. The native-calculus theorem then follows from the existing `pra_iff_native`. An ordinary Lean theorem about real spaces is a different result and does not replace this endpoint.

No suitable existing topological Sperner implementation was located in the inspected ConciseIPRA sources or repository searches. The repository's arithmetic and logical infrastructure is reused; the finite topology remains new formalization work. Draft ZIP directory metadata was inspected, but the mathematical contents of those archives were not imported.

The first-order presentation uses finite numerical inputs. Quantitative infinite maps are treated schematically for fixed primitive-recursive evaluators and moduli. The plan does not postulate a primitive-recursive universal evaluator for arbitrary primitive-recursive program codes.
