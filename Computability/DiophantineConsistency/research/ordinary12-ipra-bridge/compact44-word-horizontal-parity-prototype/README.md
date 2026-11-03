# Horizontal physical field-column parity

`CompactWordHorizontalParity.horizontal_even` proves in every model of IΣ₁
that, for a marked compact word with `1<N`, `s<N`, and a definable Boolean
dummy function, each in-range physical normalized block has an even
radix-`2^67` digit at every phase `1065+u` for `u<8`. No high-mask no-carry
or complete `PackingInput` premise is assumed.

At these phases the selector-band contributions have even parity, the
remaining bare shifts 62 and 8849 read matched east/west source bits, and
the whole-cell temporal contribution is zero by exact low-mask support.
The proof uses the checked physical-block/raw-column identity and the actual
low-slot bridge. It covers these eight phases only; the horizontal marker at
1073, vertical marker, target and anchor phases, complete high-mask safety,
graph zero and an iPRA theorem remain separate.

The bounded single-author compile (session `70217`) exited 0 without warnings
or `sorryAx`, with unchanged direct import, companion, provider-root and
mixed-overlay guards. Its named axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. Commands, source/object hashes,
dependency scans, log and inventories are retained. The providers' package,
transitive, dynamic and between-observation ancestry is inherited; `/tmp`
paths are ephemeral. This is not a paired replay or complete closure audit.
