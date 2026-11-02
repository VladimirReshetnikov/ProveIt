# Exploratory four-field and local-matching transport

`CompactRowMatch.lean` proves `four_fields`: for any `IΣ₁` model and old row index `i < 942`, the four compact field lookups at `rowLookup i` equal the horizontal or vertical permutation lookup applied to the old west, north, east, and south model color lookups. This uses the independently audited table/lookup parent and the author-only standard-row and model field-cast arguments included in this source.

The same source proves `horizontal_match_iff` and `vertical_match_iff`. Each theorem takes two old model indices below 942. The horizontal result additionally assumes old east and west colors below 250; the vertical result assumes old south and north colors below 439. Under those explicit premises, equality of the respective compact fields is equivalent to equality of the old fields. These are local conditional facts, not existence of a matching neighbor or a wraparound proof.

Author-only Lean session 35286 exited 0 for the four-field draft, and session 22948 exited 0 for the complete matching source. Both printed only `[propext, Classical.choice, Quot.sound]` for every named theorem, without warnings or `sorryAx`; no object or raw tool transcripts were retained. The compiled source is included in full because the earlier exploratory files had no retained objects. No paired replay or independent client audit has yet been conducted.

The separate obligations include deriving the color bounds for all actual old-table rows; ensuring matching neighbors and the horizontal/vertical wrap; all-model tiling transport; and the compact calibration and 12-variable iPRA endpoint. Independent JSON-to-Lean finite-table binding and provider limitations remain as documented for the paired lookup parent.
