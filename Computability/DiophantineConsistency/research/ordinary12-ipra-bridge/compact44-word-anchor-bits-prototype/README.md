# Fixed compact payload anchor bits

`CompactWordAnchorBits.value_anchor` proves in every model of IΣ₁ that
the seven payload bits 34 through 40 are one whenever the four input fields
have their specified 8-, 9-, 8- and 9-bit bounds. The proof bounds the
lower 34-bit portion and treats the upper portion as the constant 127.
`row_anchor` applies this to the actual table payload for any model row
`a < 943`, using the checked finite table bounds and row lookup; no word
matching or high-mask assumption is used.

`CompactWordCleanSupport.word_outside_bad` proves without a mask assumption
that every digit of the actual represented compact word outside the coarse
`CleanGeometry.Bad` set is zero. It uses the explicit constructed-cell
support, not the low-mask decoding direction.

`CompactWordAnchorParity` combines that support with the existing exact
anchor-phase geometry, physical zero-carry column theorem, the checked fixed
bits and cyclic index identities. Under a `CompactWord`, explicit `N>1` and
`s<N`, Σ₁-definable row/dummy functions, and globally Boolean dummy values,
the actual normalized block digits at phases 2195 and 3296 are even for
every `j<N`. In each case the surviving odd bare source and the temporal
source are fixed one, with the latter taken from the in-range cyclic stride
predecessor. `CompactWordAnchorHigh` uses the exact symbolic high-mask digit
one at each phase to prove local `NoCarry` there. These results do not prove
global high-mask disjointness, a graph zero or an iPRA theorem.

The first two guarded attempts failed on an incorrect namespace and then
local numeral/cast reductions; their exact failed sources and logs are
retained. Corrected attempt 03, session `50087`, exited 0 without warnings
or `sorryAx`. Both named axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`; sampled direct dependency/companion
guards were unchanged. This is an incremental single-author check with
inherited provider, package, transitive, dynamic-loading and
between-observation ancestry, not an independent paired replay or fully
authenticated source/object closure. The `/tmp` provider paths are ephemeral.

The no-mask support, physical anchor parity and local high-mask clients
compiled successfully in sessions `60796`, `74083` and `61508`,
respectively. Their named axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`; sampled direct guards were unchanged.
The latter two runs also checked their recorded mixed project union,
overlap comparisons, selected root inventories and post-run hashes. Their
commands, observations and logs are retained in the `support-attempt01`,
`parity-attempt01` and `high-attempt01` directories. The same single-author,
transitive/package/dynamic ancestry and independent-replay limits apply.
