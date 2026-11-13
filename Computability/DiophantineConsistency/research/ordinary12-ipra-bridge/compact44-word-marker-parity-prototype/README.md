# Physical parity at both compact field markers

`CompactWordMarkerParity.lean` proves that every in-range physical transport
block of a marked compact word has even radix-`2^67` digits at the two
marker phases 1022 and 1073. The word must have `1<N`, `s<N`, and definable
Boolean dummy inputs; no high-mask no-carry or full packing hypothesis is
assumed.

The marker-source lemma uses the checked fact that payload bits 34–40 are
one on every bounded compact row. At phase 1022, the bare shift 30 and the
whole-cell temporal shift read fixed-one marker bits. At phase 1073, the
bare shifts 62 and 8849 read fixed-one marker bits, and the temporal source
is absent by the exact low support. The checked physical/raw column and
low-slot bridges identify these contributions with the actual physical
block. Both sums are therefore even.

Together with the separate ordinary field-phase parity lemmas, this handles
the ten vertical positions 1013–1022 and the nine horizontal positions
1065–1073. It does not alone prove the other high-mask phase classes, the
complete high-mask condition, a graph zero or an iPRA derivation.

The guarded single-author run, session `49308`, exited 0 without warnings or
`sorryAx`, with unchanged sampled direct dependency/companion, selected
provider-root and mixed-overlay guards. Its three named axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`. Source/object hashes,
commands, dependency scans, log and inventories are retained. Provider
package, transitive, dynamic and between-observation ancestry is inherited;
`/tmp` provider paths are ephemeral. This is not a paired replay or complete
closure audit.
