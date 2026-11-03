# Origin and low-mask fields for base and pulsed compact words

`CompactWordLowFields.lean` proves the following for a supplied
`CompactWord row N s` in a model of IΣ₁:

* The base cell at zero is positive and satisfies the special origin
  no-carry condition against `CompactConcreteIncrement.mask + 1` after
  subtracting one from the cell.
* Every base cell with index below `N` is no-carry against the concrete low
  mask.
* After adding `2^(67*1063) * δ j` to each base cell, all of the same facts
  hold if `δ` is Boolean and nonzero only at positive indices.

The non-origin no-carry statement is actually proved for **all** indices
below `N`, a stronger range than `PackingInput.low` requires. The theorem
does not assert a complete `PackingInput`: dimensions, product and cell-sum
bounds, block positivity, both high-mask fields, and subsequent rank and
graph-zero obligations are not established by this client. Nor is it an
internal iPRA derivation.

The bounded single-author build, tool session `79579`, exited 0 without
warnings or `sorryAx`; both named axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependency and companion guards
were unchanged. The command, source/object hashes, dependency listing,
compiler output and receipt are in `observations/attempt01`. The origin,
pulse, base low-mask and other providers' package, transitive, dynamic-loading
and between-observation ancestry remain inherited. This is not a paired
replay or an independently authenticated full dependency closure.
