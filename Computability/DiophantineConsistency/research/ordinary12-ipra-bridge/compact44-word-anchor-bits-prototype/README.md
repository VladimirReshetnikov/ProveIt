# Fixed compact payload anchor bits

`CompactWordAnchorBits.value_anchor` proves in every model of IΣ₁ that
the seven payload bits 34 through 40 are one whenever the four input fields
have their specified 8-, 9-, 8- and 9-bit bounds. The proof bounds the
lower 34-bit portion and treats the upper portion as the constant 127.
`row_anchor` applies this to the actual table payload for any model row
`a < 943`, using the checked finite table bounds and row lookup; no word
matching or high-mask assumption is used.

This establishes the fixed bits needed by marker and distant-anchor phase
arguments; it does not by itself establish physical raw-column geometry,
even parity of a normalized block, high-mask disjointness, a graph zero, or
an iPRA theorem.

The first two guarded attempts failed on an incorrect namespace and then
local numeral/cast reductions; their exact failed sources and logs are
retained. Corrected attempt 03, session `50087`, exited 0 without warnings
or `sorryAx`. Both named axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`; sampled direct dependency/companion
guards were unchanged. This is an incremental single-author check with
inherited provider, package, transitive, dynamic-loading and
between-observation ancestry, not an independent paired replay or fully
authenticated source/object closure. The `/tmp` provider paths are ephemeral.
