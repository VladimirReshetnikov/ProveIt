# Compact44 carry input for the temporal rotation

`CompactTemporalConstructedCarry.temporal_product_carry` joins the exact
symbolic-product carry construction with the existing all-model bit rotation.
For any model `n`, exponent `e` and source `C`, it assumes `n>0`, positive
`M = 2^(67*n)-1`, `C < 2^(67*n)`, and every in-range radix-`2^67` digit of
`C` at most `3`. It constructs the heterogeneous `CarryInput` with carry
bound `1` for the exact cyclic remainder

```
((paramKernel rho + 2^e) * C) mod M.
```

The temporal word is the existing bit rotation `temporalWord n e C`. Its size
bound follows from the source bound, and its congruence to `2^e*C` follows
from the rotation theorem; neither is an extra premise. No opposite-band,
bare-column, temporal-digit or incoming-carry contribution is assumed zero.
The result does **not** construct `C`, prove its bound or digit cap, give the
per-cell selector/copy identities, prove the other packing conditions, bind
the retained coefficient bytes, or establish a graph zero or an iPRA theorem.

## Build observation

On a fresh symlink overlay of the word-cell author provider, compiler session
`84331` actually exited 0 rebuilding the exact prior
`CompactConstructedCarryInput` source, and session `66585` actually exited 0
compiling this client. Both used Lean 4.32.0 with `-M3000 -j1`, async
elaboration disabled and a 120-second timeout. Their retained logs contain
the expected axiom reports, no warning and no `sorryAx`. The client report
lists `propext`, `Classical.choice` and `Quot.sound`.

The checked source SHA-256 is
`f9773799389187b29bffa91c18ca8d03ca1e3cb79844a9f2e98b17008aa7ca1a`;
the client object SHA-256 is
`d1c2ed2f9a0575a0ce157ae40707465ac9286bfe674a1dc5226beed9c49991a1`.
The rebuilt carry-input object SHA-256 is
`1247ce7559aafd4a1199f224e269b369afe16286b7865d6961962bb5924dd59e`.
Before the build, both new module slots and their listed companions were
checked absent in the overlay, seed and package. Five direct input object
hashes were sampled before and after and agreed; their values and resolved
paths are in [terminal-observation.json](terminal-observation.json).
This exploratory check did not record a `lean --deps` query or enforce
continuous guards. It is a single-author incremental observation with
inherited project/package/transitive/dynamic ancestry, not a paired replay
or complete provider audit.
