# Bound for the symbolic MC byte reconstruction

`CompactLowByteBound.low_lt_byte_power` proves in Lean that the symbolic
low mask `CompactSymbolicPorts.lowNat` is less than `256^73759`. It first
uses the checked low-digit bounds and length to show
`lowNat < (2^67)^8807`, then compares the exponents without evaluating the
590,069-bit power. This supplies the **size premise** for applying the
generic radix-window reconstruction theorem to any byte list of length
73,759. It does not provide such a list or prove any byte matches, and does
not bind a file, gzip payload, JSON, PDF or iPRA endpoint.

The bounded mixed-provider author run `observations/attempt02` exited 0
without warnings or `sorryAx`; direct dependency and companion guards and
the separately inventoried generic provider were unchanged at the recorded
points. The source SHA-256 is
`a52823b786004e9d3feba5b844bcaee9d09b688984084bd16b88bb1253fe8fcd`
and the object SHA-256 is
`087cb91ad4dfc367a66a4b090e37140f6d68b1629318a81cfa8ffec233775f49`.
The named axiom reports are `[propext, Classical.choice, Quot.sound]` in
Lean's metatheory, not object-theory axioms.

Attempt01 produced an object but emitted an exponentiation-threshold
warning, so its wrapper rejected it; its source, log and receipt are retained.
Attempt02 replaces the implicit exponent comparison with explicit `omega`
steps. This is an author-side check inheriting symbolic, package and dynamic
provider ancestry, not a paired replay or complete ancestry audit. Guard
checks are point-in-time.
