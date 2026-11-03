# Positive cells and normalized blocks for a compact word

`CompactWordBlockPositivity.lean` proves that a compact cell is positive
whenever its row is below 943 and its dummy digit is Boolean: the row's own
selector digit is one. Consequently, for a supplied `CompactWord`, every
normalized block is positive for both the zero-dummy base cell family and
the family with an arbitrary nonnegative pulse added. Each block contains
the cell at its cyclic temporal predecessor, and `CompactWord` supplies both
positive word length and an in-range row at that predecessor. This includes
the origin block required by `PackingInput.blk_pos`.

The theorem proves positivity only. It does not supply the cell-plus-block
bound, either high-mask no-carry condition, a complete packing, a graph zero,
or an internal iPRA derivation.

The bounded single-author build, tool session `78416`, exited 0 without
warnings or `sorryAx`; both named axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Its direct dependencies and complete
selected mixed overlay were unchanged across compilation; the earlier full
338-file word/controller overlap comparison found no conflicts. The source
and object hashes, complete overlap and overlay inventories, command,
dependency list, compiler log and receipt are in `observations/attempt01`.
The model, package, transitive, dynamic-loading and between-observation
provider ancestry are inherited; this is not a paired replay or an
independently authenticated full closure.
