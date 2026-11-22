# Scope and predecessor comparison

Source revision used for the comparison:
`3ee850b4c2d650cf01263823fd5415963747c5d0`.

Directly inspected source:

- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/StrongMinimizer.lean`, lines 1--95, blob `5f7bce028b37579a1c5c1773de603c0e7302c191`.
- Its header explicitly retains the obligation to identify a nonnegative residual `R` with the objective gap in the signed decomposition `I + R(y)`.

Existing work already covers finite nets, least argmin, strong-convexity uniqueness, regular names, finite Hausdorff distance, and numerous branch-free polynomial-root set observations. These are credited as infrastructure, not claimed as new results.

The concrete extension in `convex_selector.tex` is an exact finite comparison between minimizers of two *different finite clouds*, using approximate midpoint closure and Hausdorff transfer. The comparison cancels both unknown optimum values. It yields a coherent canonical projection selector for compact convex sets, including a complete simplex-weight producer for hulls whose named vertices may merge or become affinely dependent. A moving-anchor estimate is also proved.

Search discovery found no relevant projection-selector or Tikhonov/Hoffman module, but search is not an exhaustive historical novelty proof. The report makes no priority claim. The contribution is an explicit iPRA-facing module and discharging the unknown-optimum residual adapter for this substantial application.

## Formalization status

The finite rational arguments and simplex producer have complete human proofs. The supplied Python implementation is exact and executable. The requested object-iPRA export and completed-real semantic bridge are Lean targets, not claimed kernel-checked here.

The accompanying parent package may contain a separate Lean scalar cancellation adapter. Its own validation record controls whether that adapter is kernel-checked.
