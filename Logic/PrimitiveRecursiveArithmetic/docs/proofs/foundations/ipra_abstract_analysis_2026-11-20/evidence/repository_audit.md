# Repository audit for the topology and function-space contribution

Snapshot: `5f3be02388442f16487d2dc5c2529961dd783d2b` (20 November 2026).

This is a source audit. The source files below were fetched at the pinned commit and read; their Lean modules were not rebuilt by this audit. Statements that a declaration is an object derivation refer to its inspected type and proof body, not a new compilation receipt.

## Inspected sources and scope

### [docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/04_observation_towers.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/04_observation_towers.tex)

Git blob: `d72f5c92202684e886270a47b0ef4ed077d59f68`.

Observation towers, strong carriers, continuity demands, and finite nerves are already developed. Their semantic relationship to points and topological spaces is explicitly separate from arithmetic certification.

**Consequence for this report.** We do not present observation towers or the mere finite-use principle as new contributions.

### [docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/07_topological_library.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/07_topological_library.tex)

Git blob: `4752c87d301d23290d7f7f9cb34ed20ee9588a72`.

Compactness is represented by PR nets and explicit finite covers. The manifold discussion says partitions of unity need bump approximants and denominator lower bounds. Approximate fixed points need coherence to become a named point.

**Consequence for this report.** New section constructs continuous tent partitions, derives the denominator lower bound from net coverage, and produces continuous function-space nets; no smoothness is claimed.

### [docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/12_limits.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/topology/ipra_topology_framework_2026-11-15/paper/sections/12_limits.tex)

Git blob: `d56f7d491e2c8f9b51d565ba5eacc6f047ece334`.

The packet explicitly excludes arbitrary cover extraction, automatic coherent selection, and general effective nerve or manifold theorems.

**Consequence for this report.** These exclusions remain. The additional results solve specific construction problems once quantitative cover data are supplied.

### [docs/proofs/foundations/ipra_coherent_methods_2026-11-15/paper/sections/04_lifting.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_coherent_methods_2026-11-15/paper/sections/04_lifting.tex)

Git blob: `f2b6f2ef514d4efb9f038b42e0fd1f40ff3151e3`.

Finite filtered lifting and compatible formal jets are developed, including a precise explanation why a local inverse does not automatically give quadratic improvement.

**Consequence for this report.** The new function-space and gluing results do not duplicate formal-algebraic lifting and do not claim formal series are convergent analytic functions.

### [Derivations/Lean/IPRADerivations/Foundations/StrongMinimizer.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/StrongMinimizer.lean)

Git blob: `5f7bce028b37579a1c5c1773de603c0e7302c191`.

selected_pair_closed is an actual Prf PRAAx statement, with supplied net-query, convexity, positivity and error-schedule premises; selected_residual uses the actual finite least-argmin selector.

**Consequence for this report.** Strong convexity is an explicit application premise. Its presence in a certificate interface is not a proof that an arbitrary objective has it.

### [Derivations/Lean/IPRADerivations/Foundations/CoherenceObstruction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/CoherenceObstruction.lean)

Git blob: `0697ca88bc0cba9e639d8aabb82c7a818b3ef7bb`.

sel_closed, restrict_adm and no_coherent supply object derivations for finite admissibility/persistence and the diagonal contradiction. The module expressly says the simulator-index argument establishing no computable infinite branch is not formalized.

**Consequence for this report.** Distinguish the proved finite object lemma from the external noncomputability conclusion. Our Specker example is likewise marked external.

### [Derivations/Lean/IPRADerivations/Foundations/FiniteCoverSkeleton.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/FiniteCoverSkeleton.lean)

Git blob: `804d50c52eb65c0479b946763bb9335b5417ac0d`.

skeleton_closed and rep_congr_closed derive a finite skeleton for a decidable equivalence relation with supplied finite coverage.

**Consequence for this report.** This does not make equality of arbitrary real-function names decidable. Our function-space approximants avoid deduplicating by real equality.

### [Derivations/Lean/IPRADerivations/Foundations/FiniteUseSignObstruction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/FiniteUseSignObstruction.lean)

Git blob: `8d47a6d45d79efdcb7c6fffc34bceb25195eb3e4`.

The file explicitly identifies itself as an external representation/algorithm metatheorem. It proves finite-query indistinguishability for defined oracle machines using ordinary Lean propositions, rather than Prf PRAAx object sentences.

**Consequence for this report.** The general README description of Derivations must not be read as making every declaration in every file an object-theory derivation.

### [docs/proofs/geometry/rigid_curve_convex_cover_2026-11-19/sections/existence.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/5f3be02388442f16487d2dc5c2529961dd783d2b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/geometry/rigid_curve_convex_cover_2026-11-19/sections/existence.tex)

Git blob: `412811727a01bcc48e8f528a8fd12570661bf9c9`.

A classical minimum-existence proof applies Blaschke selection, or Arzela-Ascoli for bounded Lipschitz support functions, and a further compactness argument for placements.

**Consequence for this report.** Our finite function-space approximation provides an explicit finite observation version of the regularity information; it does not supply the minimizing-body subsequence. This source is an example of a compactness use, not evidence of an incorrect claim of an iPRA derivation.

## What the new section adds

1. A rational tent-weight construction with a proved denominator bound and quantitative variation bound.
2. A continuous reconstruction map from finite coefficient vectors, nonexpansive in coefficient sup distance.
3. A concrete exterior finite cover of a uniformly bounded equicontinuous function family, with explicit size H(k) and a PR selector from observed samples.
4. Positive finite-rank approximation operators and an explicit common-modulus converse.
5. Guarded local gluing with a produced global Lipschitz bound, including an explicit evaluator and no exact sign test on a named real.
6. An exact rational error target that can be translated into the existing Prf PRAAx derivation discipline.

These are newly supplied constructions relative to the inspected framework sources. No claim of novelty in classical approximation theory, no exhaustive repository novelty claim, and no claim of completed object formalization are made.

## Changes that are additional hypotheses, not discharged obligations

- Uniform equicontinuity is supplied quantitatively; bare pointwise equicontinuity does not automatically provide its modulus.
- The domain has certified finite nets; arbitrary open-cover compactness is not converted into a PR operation.
- Local functions have bounds and local moduli; the theorem derives the gluing modulus and denominator lower bound from those data.
- A modulus for convergence or a coherent subsequence is not supplied by finite approximation.
- Choosing cover centres inside the original function family requires witnesses for occupied profile classes; the constructed centres lie in ambient continuous-function space.

## Primary references for the boundary

- Ernst Specker, *Nicht konstruktiv beweisbare Sätze der Analysis*, Journal of Symbolic Logic 14(3) (1949), 145–158. DOI: https://doi.org/10.2307/2267043 . Original publisher page: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/nicht-konstruktiv-beweisbare-satze-der-analysis/7DF80F87A63EAA248758D8C27416CED1 .
- Alexander P. Kreuzer, *From Bolzano–Weierstraß to Arzelà–Ascoli*, Mathematical Logic Quarterly 60(3) (2014), 177–183. DOI: https://doi.org/10.1002/malq.201200076 . Author preprint: https://arxiv.org/abs/1205.5429 .

Kreuzer works with second-order reverse-mathematical base theories. The present report does not transfer those equivalences mechanically to iPRA. The explicit constant-function example independently proves the computational obstruction used here.
