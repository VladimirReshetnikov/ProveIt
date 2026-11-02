# Uncompiled reverse cyclic-word draft

`CompactMarkedReverseDraft.lean` is a source-only, uncompiled draft. It proposes mapping an already existing `CompactWord` pointwise through `inverseLookup` to obtain an old-table `MarkedWord`, using the bounded local matching equivalences. The source has not been checked by Lean and may contain elaboration or mathematical errors.

The proposed input already assumes every compact index is <943 and is not 1, along with the compact word's existing cyclic east/south neighbor and wrap conditions. It does not prove row 1 is excluded, construct a cyclic word, or establish definability of the composed word. Its two imports are separately proposed paired clients; a coherent shared-provider build and independent checks are required before this draft may be compiled or used. No reverse tiling equivalence, compact calibration or 12-variable iPRA endpoint follows from this draft.
