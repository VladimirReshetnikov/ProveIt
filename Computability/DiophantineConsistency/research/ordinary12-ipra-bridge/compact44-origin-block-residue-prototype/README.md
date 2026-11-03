# Compact origin transport block is zero modulo four

`CompactKernelDivFour.lean` first proves that every term of the exact symbolic
kernel has a positive radix exponent. It follows that the zero radix digit
vanishes, and the actual symbolic kernel is divisible by four, including
after casting into an arbitrary model of IΣ₁. The proof keeps the radix
variable generic until the final specialization, avoiding expansion of the
enormous kernel numeral.

`CompactOriginBlockResidue.lean` proves that the low kernel-product half is
divisible by four, and that the high half is divisible by four when its input
satisfies the existing cell-size bound. For any compact marked row word with
`0 < s < N`, and arbitrary dummy inputs normalized modulo two, it then proves
that the actual transport block `blk ... 0` is zero modulo four. The final
summand is the temporal predecessor cell: its row cannot be marker row zero
because the marker's north and south colors differ. The other two summands
are the low and high kernel-product halves.

This supplies the residue premise of the separate high-origin transfer. It
does **not** prove ordinary no-carry of the origin block against the high
mask, any other high-mask condition, a complete packing, graph zero, or an
iPRA theorem.

The first kernel-divisibility attempt failed through kernel memory pressure
when specializing a giant radix and a divisibility-cast error; its source and
log are retained. The generic-radix retry and the subsequent block-residue
client exited 0 (sessions `24803` and `64689`), without warnings or `sorryAx`.
All named axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. Direct dependency and companion guards and the documented
mixed-provider overlay hashes were unchanged. Exact source/object hashes,
commands, dependency scans, logs and inventories are retained in
`observations/`; `/tmp` providers are ephemeral. These are single-author
incremental checks with inherited package, transitive, dynamic and
between-observation ancestry, not paired replay or complete closure audits.
