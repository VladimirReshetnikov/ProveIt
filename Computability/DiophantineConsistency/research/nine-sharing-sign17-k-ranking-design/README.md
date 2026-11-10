# K coefficient-array to symbolic ranking: proposed Lean bridge

The separately [audited external K recipe](../nine-sharing-sign17-k-coefficient-bytes/README.md)
checks that the frozen 3297-entry coefficient array decodes to the pinned K0
raw snapshot. A Lean theorem that this array represents
`CurrentKernel2011.K` is still missing.

Existing repository machinery can reduce the finite rank-verification cost:
`WangTiles942Permutation.physicalMap_bijective` proves the actual 942-position
map is a bijection; `physicalMap_zero` handles the exceptional Start tile;
`physical_lt_iff_weight` characterizes non-Start ranks by descending actual
selector weight; and `physicalWeight_strictAnti` proves the resulting
positions 1–941 are strictly descending. `CurrentKernel2011.rawWord_eq` gives
K as three sentinel powers plus the sum of 976 weighted entries indexed by
`position`.

A candidate staged kernel-checked route is:

1. Embed a finite candidate permutation/table derived from the frozen
   coefficient array, with an independently checked source snapshot. Prove
   its range, injectivity/bijection and its treatment of position 0. Check the
   941 non-Start tile weights against the table in bounded chunks, using the
   actual Lean `tile` and `selectorWeight` definitions. These are finite
   computations; no such table proof is yet present here.
2. Prove the candidate table is strictly descending. Use the existing
   bijection and `physical_lt_iff_weight`/`physicalWeight_strictAnti` to prove
   the candidate positions equal the actual `physicalEquiv` ordering. This
   avoids claiming equality solely from matching total masses or hashes.
3. Aggregate the 34 control entries and three sentinel powers, including
   every collision, to prove the frozen coefficient recipe equals
   `CurrentKernel2011.K`. Then establish its base-`2^47` digit sequence and
   compose bounded digit/byte blocks. The [external K block audit](../nine-sharing-sign17-k-block-layout/README.md)
   finds 253 blocks, 126 patterns, and a final five-digit/24-byte tail; these
   counts are external observations, not Lean theorems.
4. Keep the raw/gzip/JSON/file snapshot relationship as explicit external
   provenance unless the actual byte snapshot, parser/decompressor and hash
   checks are formalized in Lean. A theorem over a fixed byte list does not
   assert that a mutable file currently contains that list.

This is a design, not a proof of the array-to-Lean-K equality, a completed
byte binding, or any additional consistency equivalence.
