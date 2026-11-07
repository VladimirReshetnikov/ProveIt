# Ring-variable Bd explicit-unfold retry

This source-only candidate preserves the [original statement](../nine-seed38-jones-vars-bd-draft/README.md) and replaces the failed final `rfl` by explicit unfolding of the relevant `RingVars` fields and numeral-cast simplification. Rank and large sums stay opaque. The guarded compile left a residual cast equality and did not accept the theorem; the independent failure audit passed. this remains one cut binding, not named-evaluator equality or JSON/document binding.
