# Byte windows of the symbolic MC low mask

`CompactLowByteWindow.low_byte` is a Lean theorem for every natural byte
index `j`. It expresses `(lowNat / 2^(8*j)) % 256` using the two
zero-padded base-`2^67` digits adjacent to bit `8*j`, with the appropriate
shifts. `padded_digit` separately identifies every such padded digit with
the `CompactListMask.digit` support/exception formula for indices below
8,807 and with zero outside that range. `lowDigits_bounded` checks that all
underlying digits are below `2^67`. Thus future proofs can establish byte
windows through bounded local calculations, including windows crossing a
67-bit boundary, without normalizing the full 590,069-bit mask.

The proof specializes the previously checked generic `ByteWindow.byte` to
the exact list used in `CompactSymbolicPorts.lowNat`; it does **not** check
the retained MC byte literal, the number's serialization length or any
genuine file or gzip equality. No coefficient-to-PDF, JSON or iPRA result
follows from it. A separate general radix-window reconstruction theorem is
available to assemble suitable future per-window byte certificates.

The bounded mixed-provider author run `observations/attempt01` exited 0 in
2.145 seconds without warnings or `sorryAx`. The source SHA-256 is
`3a1791596e792ce719b41a67804f4de4c390d0c979db8079ccb30bf926ecbfd1` and
the output object SHA-256 is
`b03192db27e14dc487a1de4307687bb4876fab3dafd4ede9502434becf35e905`.
The direct dependency and companion guards were unchanged. The six-file
generic `ByteWindow` provider was pinned and inventoried, checked against
each same-named selected symbolic/package file with conflicts rejected, and
unchanged after the run. The named Lean metatheory axiom reports are
`[propext, Classical.choice, Quot.sound]`, not object-theory axioms. This is
one author-side check, not a paired replay or a complete audit of symbolic,
package or dynamic ancestry; guard checks are point-in-time.
