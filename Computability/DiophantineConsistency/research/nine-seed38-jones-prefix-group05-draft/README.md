# Proposed q and N preservation at d10

This source-only client proposes carrying the already checked q and N short-prefix values to their indices in `d10`, immediately before the `R` node is appended. Each step uses the generic `snoc_previous` identity, leaving all intervening symbolic sums and coefficients unevaluated. These are candidate statements; no Lean result is implied by the draft. They do not prove the value of `R`, full-recipe semantics, or any JSON/document binding.

The [guarded check](../nine-seed38-jones-prefix-group05-check/README.md) pins this source and the checked group03 provider.
