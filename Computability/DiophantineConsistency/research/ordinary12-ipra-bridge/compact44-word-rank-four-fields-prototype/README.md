# Chosen rank with concrete product bounds

`CompactWordRankFourFields.lean` applies the actual compact-cell product
bounds to the previous chosen-rank theorem. For each valid word index,
`CompactWord.tile_ne` excludes the forbidden row; the bounds then establish
the kernel-product `hi_lt` field both for the base cell and, by Boolean case
analysis, for every pulsed cell. Neither `hi_lt` fact is an additional
assumption in the resulting theorem.

The theorem still assumes **four** product/block fields for the base word:
the cell-plus-block bound, origin block positivity, and origin and non-origin
high-mask no-carry. It also assumes those same four fields for the pulsed word
uniformly over every definable Boolean selector satisfying the stated
positive and nonwrapping support conditions. The five shared scalar bounds
remain explicit premises. Under these conditions, the conclusion is a chosen
definable selector with a valid pulsed `PackingInput` and the prescribed
rank congruence. It does not prove the four remaining block fields, graph
zero, retained-byte binding, an end-to-end converse, or an iPRA derivation.

The bounded author-side build, tool session `37794`, exited 0 without
warnings or `sorryAx`. Its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. All direct dependency guards, the full
selected word/controller union overlay, the selected controller-root
inventory and the additional symbolic-kernel root inventories were unchanged.
Before compilation, all 338 overlapping word/controller provider files and
all 339 overlapping radix/overlay files had matching hashes. The complete
preflight, dependency listing, command, source/object hashes, log and receipt
are in `observations/attempt02`.

Another Lean run for the separate word-pulse equality **overlapped briefly**
with that first build because of message timing. A subsequent sole-Lean
author-side rerun, tool session `85261`, exited 0 with the same object hash,
no warnings or `sorryAx`, and unchanged direct, full-overlay, controller
root and symbolic-kernel root guards. Its separate preflight, log and
terminal receipt are retained in `observations/attempt03`. These are two
author-side runs, not an independent paired replay.

The result uses mixed providers and inherits their package, transitive,
dynamic-loading and between-observation ancestry. It is a single-author
observation, not a paired replay or independently authenticated full closure.
