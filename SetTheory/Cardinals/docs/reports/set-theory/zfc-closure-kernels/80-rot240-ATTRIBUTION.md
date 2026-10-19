# Attribution and provenance

The original compact proof calculus, set theory, source program and 254-state machine remain credited to Mira-Cult. The upstream Rocq verification remains credited to Jeff Ketchersid, and the compiler framework to Andrew James Wade. ProveIt and its earlier incoming reports retain credit for the successive source/routing/initialization reductions, compensated fold, QT loop rotation, and predecessor-bit folds that produced the exact 241-state baseline.

This investigation contributes the second transfer-plus-one rotation at inherited state 142, its composition with the 90-to-72 fold, the resulting literal 240-state table, independent source/local/initialization checks, the fresh final complete runtime replay, and the rational-cut obstruction and exact infinite-model evaluator.

The two ingredients—transfer rotation and predecessor-bit state sharing—both appear in prior work. The new contribution is this concrete composition, artifact and proof; no historical priority claim for the general techniques is made.

`reference/BusyBeaver_241_Companion_2026-10-18.zip` is preserved byte-for-byte from ProveIt commit `8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569`. It contains its own pinned 242 dependency and historical provenance. No historical receipt is relabeled as a new execution.

The generic symbolic engine and helper under `verification/` derive from the 241 companion. The helper bytes are unchanged. The engine's only adaptation is the exact new source-list count and hash and the output field labeling that source pin. The reproduction driver checks this byte-level adaptation against `reference/upstream_symbolic_runtime.py`. Its transition and induction rules are unchanged.

All inherited notices and licenses remain under `licenses/`; the prior companion retains its own unchanged license files. These files remain available for incorporation into ProveIt under the applicable original terms. No additional personal author is inferred from tool output or filenames.
