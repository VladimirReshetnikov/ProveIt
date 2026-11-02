# Exploratory standard-row correspondence

`CompactRowTransport.row_at` proves for each natural `m < 942` that the exact translated old tile at `m` equals the compact table row selected by the actual `rowIndices` lookup. It applies the audited `full_row_equality` at that index; it does not evaluate all rows again.

The corrected source was checked with the author side of `/tmp/ipra-compact-table-lookup-pair-01`, paired parent independently audited in commit `6354398167`, and the guarded Foundation package. The actual Lean session 25190 exited 0 and printed `[propext, Classical.choice, Quot.sound]` without warnings. This is an author-only exploratory check; no paired replay or independent review of this client has yet occurred. No object was retained.

The first source is retained as `failed01.lean`: session 57673 exited 1, with argument-elaboration errors in `getElem?_pos`, warnings, and a `sorryAx` report. The corrected source supplies both list and index arguments. These session observations are recorded here; raw tool transcripts are not included.

This standard-index statement by itself does not establish model-index field equality, matching-neighbor conditions, wraparound, tiling transport, compact calibration, or an iPRA theorem.
