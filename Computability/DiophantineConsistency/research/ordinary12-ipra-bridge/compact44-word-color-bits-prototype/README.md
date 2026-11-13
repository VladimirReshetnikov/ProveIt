# Forward tile-color bit equalities

`CompactWordColorBits.lean` proves the bitwise consequences of the existing
`CompactWord` adjacency conditions in every model of IΣ₁. If two in-range
rows satisfy its vertical predecessor relation, each of the first nine
south bits of the current row's payload equals the corresponding north bit
of the predecessor payload. For the horizontal predecessor relation, each
of the first eight east bits equals the corresponding west bit. The indices
`u < 9` and `u < 8` are model elements, not merely a finite scan.

The proof uses the actual 943-row table, bounded-row casting, the checked
payload/field slices, and the existing `CompactWord.south` and `.east`
relations. It is a forward construction lemma; it does not yet identify the
packed word's physical stencil columns, prove output parity, high-mask
no-carry, graph zero, or an iPRA theorem.

The guarded single-author build (session `78097`) exited 0 without warnings
or `sorryAx`, with unchanged sampled direct import and companion guards. Both
named axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. Source/object hashes, command, dependency listing, compiler
log and terminal receipt are in `observations/attempt01`; the `/tmp`
providers are ephemeral. Package, transitive, dynamic and between-observation
ancestry is inherited; this is not an independent paired replay or a complete
closure audit.
