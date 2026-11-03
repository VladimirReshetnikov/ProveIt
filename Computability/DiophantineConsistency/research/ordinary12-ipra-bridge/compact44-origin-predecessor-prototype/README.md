# Compact marker predecessor and cell low residue

`CompactOriginPredecessor.lean` proves that compact table row zero has north
color 435 and south color 1. For a model `CompactWord row N s` with
`0 < s < N`, the cyclic vertical predecessor `cyc N 0 s` cannot be row zero:
otherwise the required south/north matching at the marker would identify 1
with 435. This is a property of the pinned compact table and the checked
`CompactWord` interface; it applies in every model of IΣ₁.

The same module proves `packedCell a d % 4 = 0` whenever `a ≠ 0` and `d ≤ 1`.
At non-marker rows, the first radix-`2^67` selector digit is zero, and the
proof reduces modulo four through that radix. Combined with the predecessor
lemma this supplies the low residue of the temporal predecessor cell. It
does not alone prove the low residue of the full `blk 0`, the ordinary or
special origin high-mask no-carry fields, a complete packing, graph zero or
an iPRA theorem.

Guarded author attempts 01 and 02 failed on local coercion and exponential
rewrite issues; their exact sources and logs are retained. Attempt 02 also
printed the evaluated first row `(2,435,3,1)` as a diagnostic, not as a
substitute for proof. Corrected session `19943` exited 0 with unchanged
sampled direct dependency and companion guards, no warnings or `sorryAx`,
and only `propext`, `Classical.choice` and `Quot.sound` in four named axiom
reports. Source/object hashes, commands, dependency scans and logs are
retained. The providers' package, transitive, dynamic and between-observation
ancestry is inherited; `/tmp` paths may disappear. This is not an independent
paired replay or a complete closure audit.
