# Uncompiled supplied-cyclic-word bridge

`CompactCyclicBridgeDraft.lean` is source-only and has not been checked by Lean. It proposes upgrading a supplied positive-period compact cyclic word with bounded rows and given east/south matching to one excluding compact row 1, then using the drafted inverse direction to obtain a marked old word. The additional row-lookup Σ₀ instance is also uncompiled.

The imports in this proposal are from separately checked or drafted clients, not yet a coherent audited combined provider. In particular, the reverse-word client is uncompiled, and the model exclusion is currently only author-side exploratory evidence. Coherent paired rebuilds and an independently checked combined dependency closure are required before this client can be used.

The proposal assumes an existing function, a positive period, bounded tile indices, a marker, and supplied cyclic east and south matching. It does not construct a word or tableau, prove the hypotheses, establish definability of lookup composition with a represented word, calibrate the compact checker, or prove the 12-variable iPRA endpoint.
