# Selected ProveIt providers and trust boundaries

The accompanying `source_manifest.json` pins **23 inspected source files**,
including exact Git blob IDs and SHA-256 hashes. It is a selected provider map,
not a transitive dependency lockfile. Upstream source files are not duplicated
in this archive.

The object-language sources were read at commit
`b2341af5370cd8a43f72ebb2341c0d7d7395b634`. Four newer framework sections were
fetched at `83421593771f877bc1ae98f4229eb35507bff05b`.

## 1. The arithmetic and logical target

[PR.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean) defines `PR`, `PTm`, `PRAAx`, the primitive-recursion equations,
and `PRA.qfInd`. [Deduction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean) defines the intuitionistic
first-order proof type `Prf` and its equality, quantifier, substitution, and
structural rules. These are the target interfaces for a genuine embedded
iPRA derivation. An ordinary Lean theorem about real or rational numbers
does not automatically inhabit `Prf PRAAx`.

## 2. Existing finite object-language probability

These files contain source declarations with actual embedded proof types.
They were inspected here; the upstream package was **not rebuilt** during
this task. The standalone kernel in this deliverable was independently built.

| Provider | What the selected endpoints supply | Boundary |
|---|---|---|
| [FiniteKernel.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/FiniteKernel.lean) | `pr_evaluator`, `weighted_average`: quantifier-free comparisons of fixed finite expectations and natural-weight normalization. | The name `pr_evaluator` does not mean a universal evaluator for all PR programs. |
| [Expectation.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/Expectation.lean) | `exp_add`, `exp_mono`, `markov`, `chebyshev`, `cauchy_schwarz`, `second_moment`. | Finite weights and sums, with denominators cleared; analytic completion is separate. |
| [WeakLaw.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/WeakLaw.lean) | `monte_carlo`, `dev_identity`, `weak_law`: product-sample moments and the finite weak law. | Transfer to continuous presentations needs moment and event certificates. |
| [FirstCrossing.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/FirstCrossing.lean) | `cover`, `disjoint`, `crossing_bound`: the exact first-crossing Boolean decomposition. | Provides finite event arithmetic, not an infinite stopping-time theorem. |
| [KolmogorovAssembly.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/KolmogorovAssembly.lean) | `assembly`: sums supplied crossing-step bounds by finite Fubini and disjointness. | Product splitting and the terminal variance identity are not established by this file alone. |
| [KolmogorovIid.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/KolmogorovIid.lean) | `past_hyp` and `future_mean`: the past crossing condition and centered future increment for one iid crossing step. | This file alone is not the completed maximal inequality. |
| [NormalMoments.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/NormalMoments.lean) | `df_fact`, `edf_eq`, `moment_quotient`: arithmetic of the Gaussian moment coefficients. | The source explicitly excludes the integrals identifying these numbers with Gaussian moments. |
| [CompleteSquare.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/CompleteSquare.lean) | `hellinger_square`, `product_square`: denominator-cleared polynomial identities. | The source explicitly excludes Gaussian normalization integrals. |
| [ProductReplacement.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/ProductReplacement.lean) | `replacement_identity`, `replacement_bound`: finite product telescoping and bounds. | Characteristic functions, damping and smoothing are excluded. The report uses an expectation-replacement proof, not a claim that this file already proves the CLT. |

The report's maximal-inequality argument is a human proof whose finite
pieces can reuse these providers. The map does not assert that one imported
file already contains the entire continuous theorem.

## 3. Earlier continuous-probability reports

- Expected value: [manuscript](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/expected_value_ipra_2026-11-16/paper/expected_value_ipra.tex), [effective-integration section](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/expected_value_ipra_2026-11-16/paper/sections/10_effective_integration.tex), and [status/README](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/expected_value_ipra_2026-11-16/README.md). These provide finite expectation and L1/quadrature/tail arguments. The packet describes its own Lean artifacts as uncompiled blueprints. Later `Derivations` sources above have a different status.
- Normal distribution: [manuscript](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/normal_distribution_ipra_2026-11-16/paper/normal_distribution_ipra.tex), [Gaussian-core section](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/normal_distribution_ipra_2026-11-16/paper/sections/03_gaussian_core.tex), and [status ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/normal_distribution_ipra_2026-11-16/STATUS.md). These contain human analytic arguments and exact certificate plans; they are not imported as completed object-language Gaussian analysis.
- Central limit theorem: [manuscript](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/central_limit_ipra_2026-11-15/paper/central_limit_ipra.tex) and [status/README](https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/central_limit_ipra_2026-11-15/README.md). The earlier packet discusses stronger Berry--Esseen estimates, but identifies its Lean artifacts as uncompiled blueprints. The present report supplies its own simpler Lindeberg replacement and smoothing proof and does not treat those stronger estimates as already checked dependencies.

## 4. Newer continuous-mathematics frameworks

The following sections are research-report providers. They contribute
representations, human arguments, and formalization interfaces; they are
**not a complete object-iPRA continuous-measure library**.

| Current section | Relevant contribution |
|---|---|
| [Observable-analysis foundations](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_observable_analysis_2026-11-20/paper/sections/foundations.tex) | Separates internal arithmetic, presentation schemas, and semantic adequacy; finite compilation and explicit-loss completion. |
| [Coherent measured partitions](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_observable_analysis_2026-11-20/paper/sections/measure.tex) | A shared event algebra, L1 completion, effective convergence, and integration/Fubini interfaces. |
| [Probability sort](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_observable_analysis_2026-11-20/paper/sections/model_probability.tex) | Finite transport and explicit nets of probability laws; its own text records the construction as human proof plus implementation outline. |
| [Measure transport](https://github.com/VladimirReshetnikov/ProveIt/blob/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_measure_transport_2026-11-20/paper/sections/03_measure.tex) | Dyadic completion, effective countable unions, conditional averages, quantitative Vitali, and density-from-mass contracts. |

## 5. Reproduction and limits of this manifest

For each entry, fetch `repository_path` at its full `commit` and compare its
Git blob ID and SHA-256 with the manifest. All pinned local source files
matched their repository blobs exactly. The four fetched working copies had
one additional trailing LF byte; removing exactly that byte reproduced the
reported Git blob IDs. The manifest records both the canonical repository
hash and the materialized-copy hash, without silently conflating them.

Inspection here means reading the listed definitions, endpoint statements,
selected proofs, and formalization-status descriptions. It is not a fresh
kernel check of the whole upstream dependency graph or an audit of every
claim in the earlier research manuscripts. No upstream repository mutation
was performed.
