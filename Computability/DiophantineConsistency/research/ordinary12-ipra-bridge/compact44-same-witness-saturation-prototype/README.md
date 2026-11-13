# Exploratory same-witness symbolic saturation and congruence

`CompactSameWitnessSaturation2.lean` combines the exploratory
`FreeJGraphCongruenceExplore.fixed_symbolic_aligned` with the separately
exploratory `CompactSymbolicGraphSaturation.graph_saturation`. For the fixed
symbolic beta, low and high masks, arbitrary natural `K`, positive graph
coordinates and the literal graph zero, the fixed theorem obtains the same
model `N,w` for the radix and repunit identities, graph alignment, bound and
weighted congruence, low-digit bounds, and both global `NoCarry` assertions.
The generic theorem additionally takes the explicit model beta identity and
natural low/high symbolic equalities. The exact statements, graph index and
all casts are in the source.

The first direct fixed-tuple attempt is retained under `observations/attempt01`:
its Lean session 95362 exited 134 with an interpreter memory exception at the
3,000 MB threshold. The successful source first proves the generic theorem
and only then specializes it. Session 43471 actually exited 0 without
warnings, and both named reports were `[propext, Classical.choice,
Quot.sound]`; the exact observed output and command are in `observation.txt`.
The earlier attempt to use two separate project library roots exited 1
before compilation because Lean selected the first namespace root and could
not find `CompactGraphDerivedRadix.olean`; a fresh symlink overlay fixed the
lookup. Both prerequisite sources were rebuilt on the same author-side
radix overlay before the successful client compile.

This is single-side exploratory evidence, not an independently reviewed
coherent paired build. `K` and the symbolic masks have not been bound to
retained bytes; no graph-specific weighted-word decomposition, fractional
rotation, carry reset, compact decoder, machine equivalence or internal iPRA
proof follows. A source-closure plan, independently reviewed launcher, paired
replay and independent artifact audit are still required.
