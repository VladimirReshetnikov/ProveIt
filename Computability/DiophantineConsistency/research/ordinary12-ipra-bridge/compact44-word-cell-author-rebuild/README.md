# Compact44 word-to-local-cell author build

The guarded author-side build, tool session `28542`, actually exited 0 with
`PASS_AUTHOR_WORD_CELL`. It first rebuilt `CompactForwardCellInputs`, then
compiled `CompactWordCellClient` on the same fresh overlay of the
marked-suffix provider. Thus the earlier coefficient-overlay and word-overlay
objects were not mixed. The source comment saying the client is uncompiled is
stale; the checked bytes were retained unchanged from the draft.

In any model of IΣ₁, the client defines a payload using the four
`compactField` lookups of `CompactWord`, proves it agrees with the finite
decoder row, and proves its Σ₁ definability. For a Σ₁-definable word, each
fixed selector-position and payload-bit function is also Σ₁-definable. At
every position `j < N` of a `CompactWord`, the finite actual selector-and-copy
coefficient aggregate is `1 + 2^51`. This last result uses the word's row
bound; it does not establish the subsequent packed cell, no-carry/mask and
neighbor transport, graph zero, retained coefficient binding or iPRA result.

The build uses a fresh symlink overlay, freezes both sources, checks target
absences and direct provider/companion slots, and runs each Lean child with
`-M3000 -j1`, async elaboration disabled and a 600-second timeout. Both logs
have no warnings or `sorryAx`; their 11 named axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. The complete retained result
SHA-256 is `211454dc83aa90a0cb58ba5a6bf4013ac37b2018389ac1593ea9c0df6f760526`.
`CompactForwardCellInputs.olean` has SHA-256
`b432fcfa979dd53d73961d4cb09dc02e2f2949a145ce35ed726b3838dea5b1bd`;
`CompactWordCellClient.olean` has SHA-256
`56ced49c140437f4080d25499828285386e881389e6ea6a418e18dab3d46bed8`.
Frozen sources, logs, preflight, direct guards and per-module and final
receipts are retained under `observations/author/`.

The author-side no-Lean `audit.py` passed its post-run check of the retained
and live sources, logs, named reports and direct guards. The build and audit
are single-author observations, not a paired replay, independent Lean
reconstruction, or complete transitive/project/package/dynamic-provider
authentication. The marked-suffix provider's ancestry and point-in-time guard
limitations remain inherited.
