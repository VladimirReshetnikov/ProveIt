# Base low-mask no-carry for the compact cell

`CompactBaseLowNoCarry.lean` proves, in every model of IΣ₁, that
`NoCarry (packedCell a 0) CompactConcreteIncrement.mask` holds whenever the
row `a` differs from the forbidden selector 1. Each local cell digit is
Boolean; a nonzero digit lies in the concrete mask's support; and the mask
digit at each supported position is even. `bsum_noCarry` then joins these
per-digit facts across all 8807 radix-`2^67` slots. The stated mask is the
exact symbolic concrete mask defined by the imported provider.

For a valid `CompactWord`, its `tile_ne` field supplies the row condition at
each cell index below `N`. This result proves the **base** local low-mask
no-carry fact. It does not by itself prove the special origin condition with
`X 0 - 1` and `mask + 1`, a full `PackingInput`, product/high-mask safety,
graph zero or an internal iPRA proof. The separate pulse client additionally
uses this base fact to establish low-mask safety after the prescribed single
dummy pulse.

The first bounded attempt failed on two local Lean rewrites; the source and
compiler output are retained in `observations/attempt01`. The corrected
single-author build, tool session `77602`, exited 0 without warnings or
`sorryAx`; its four named axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependency and companion guards
were unchanged; source and object hashes, command, dependency listing and
compiler log are in `observations/attempt02`. The digit-support, packed-cell,
and symbolic-mask providers and their package, transitive, dynamic-loading,
and between-observation ancestry are inherited. This is not a paired replay
or an independently authenticated complete dependency closure.
