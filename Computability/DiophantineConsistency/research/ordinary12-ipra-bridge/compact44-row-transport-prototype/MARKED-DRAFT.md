# Uncompiled cyclic-word transport draft

`CompactMarkedTransportDraft.lean` is an uncompiled source draft. It proposes applying `rowLookup` pointwise to an already existing old-table `MarkedWord`, showing the bounded image avoids compact row 1, and transporting the existing east and south cyclic matching premises using the bounded local equivalences. It does not assert that a marked word exists or establish those original neighbor or wrap premises.

The draft also does not establish the reverse direction or that the transformed word has the definability required by later arithmetic model arguments. It depends on a successfully compiled and coherently paired `CompactRowComplete` object, which is not yet available. No Lean process has checked the draft.
