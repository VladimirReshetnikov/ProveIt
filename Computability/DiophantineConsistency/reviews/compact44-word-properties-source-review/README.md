# Compact44 word properties: source-only review

This is a source inspection of
[`CompactWordProperties.lean`](../../research/ordinary12-ipra-bridge/compact44-word-properties-prototype/CompactWordProperties.lean),
SHA-256 `dcebdfa93dbc183c3da216c305a74e457b4e4a0c2f34cedf9ad4cefb198b677a`,
against the workspace versions of
[`CompactConstructedWord.lean`](../../research/ordinary12-ipra-bridge/compact44-word-constructed-prototype/CompactConstructedWord.lean)
and [`CompactMarkedTransport.lean`](../../research/ordinary12-ipra-bridge/compact44-row-transport-prototype/CompactMarkedTransport.lean).
The latter source hashes are respectively
`5b6418271fd049f0327d472a208ef45c5cd0a589d71ae8ff98853d07bd42f72e`
and `3c520db71225576edeb51f4855d42f644fb7479d4e9df634e6735b6185670fb6`.
No statement or missing-hypothesis issue was found in this inspection.

* `word_definable_length` proves definability as a function of the model
  length `N`, for fixed Σ₁-definable row and dummy functions. It does not
  state uniform definability over those functions.
* `word_cap` assumes both functions are Σ₁-definable and `k < 8807*N`. The
  quotient/remainder decomposition selects cell `k/8807 < N` and position
  `k%8807 < 8807`, so the cited cell-digit cap applies. The claim is
  vacuous when `N=0`.
* `marked_word_origin` assumes `CompactWord row N s`; its proof uses only
  positive length and `row 0 = 0` from that structure. It allows arbitrary
  dummy inputs because the origin selector does not depend on them. The
  constructed cell normalizes each dummy to `dummy j % 2`, so no Boolean
  bound on the input dummy function is implicitly required.

This inspection does not replay Lean, audit the source/object dependency
closure, or independently authenticate provider ancestry. It does not
construct a `CompactWord`, establish low- or high-mask and product
conditions, or prove the graph-zero or iPRA endpoint. The separate author
compile observation and its limitations are recorded in the
[prototype README](../../research/ordinary12-ipra-bridge/compact44-word-properties-prototype/README.md).
