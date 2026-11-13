# High-mask origin transfer for marked compact words

`CompactHighOriginMarked.lean` combines the actual origin-block residue with
the symbolic high-mask residue. In every model of IΣ₁, for any `CompactWord`
with `0 < s < N`, ordinary `NoCarry (blk j) highNat` at **every** `j < N`
implies both the special `NoCarry (blk 0) (highNat - 1)` origin field and the
ordinary non-origin high-mask field. The client proves this for three related
cell families:

* normalized represented cells for an arbitrary dummy function;
* the zero-dummy `baseCell` family; and
* the explicit `pulsedCell` family when every pulse is Boolean.

The pulse theorem uses the separately checked equality between normalized and
explicit-pulse cells. The stronger all-index ordinary high-mask no-carry
condition is an **explicit assumption**; the client does not prove it, a
complete packing, graph zero, or an iPRA derivation. The two separate high
fields of a packing may therefore be replaced by one all-index condition,
but that condition is still the substantive open high-mask obligation.

The guarded author compile (session `72372`) exited 0 without warnings or
`sorryAx`; the three named axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Its direct dependency/companion guards
and 517-name mixed-provider overlay inventory remained unchanged. The
source/object hashes, dependency scan, command, compiler log and terminal
receipt are retained in `observations/attempt01`; `/tmp` provider paths are
ephemeral. This single-author build inherits package, transitive, dynamic and
between-observation ancestry and is not an independent paired replay or a
complete dependency-closure audit.
