# Compact44 physical-column theorem: source-only review

This inspection covers
[`CompactMarkedPhysicalColumn.lean`](../../research/ordinary12-ipra-bridge/compact44-marked-physical-column-prototype/CompactMarkedPhysicalColumn.lean),
SHA-256 `da699738add12c3caeb1b53c7d87447d02a73e9dbcf2c307323f17ecd34d57b1`.
No hidden mask or full-packing assumption was found in the inspected source
and immediate supporting statements.

The theorem assumes Σ₁-definable row and dummy functions, `CompactWord row
N s`, `1 < N`, `s < N`, and `dummy j ≤ 1` for **every** model index `j`.
It proves for each `j<N` and `q<8807` both zero cyclic carry at the global
phase `8807*j+q` and equality of the actual normalized `blk` subdigit to the
corresponding raw symbolic-stencil column. The temporal exponent is
`67*(8807*s)`, matching the physical block shift `590069*s`.

The [partial transport source](../../research/ordinary12-ipra-bridge/compact44-partial-packing-transport-prototype/CompactPartialPackingTransport.lean)
at SHA-256 `e8fcd78dccb6592e68eb8f38b41d7d41615d5634ce8c18a86045e3eea5fb945a`
defines `TransportInput` using only length/stride, product-size, cell-sum and
source-origin conditions. It does not include `PackingInput`, a mask, or a
`NoCarry` condition. The physical-column client derives those fields from
its explicit word hypotheses and the imported size/product results. The
[aligned zero-carry source](../../research/ordinary12-ipra-bridge/compact44-aligned-stencil-zero-carry-prototype/CompactAlignedStencilZeroCarry.lean),
SHA-256 `547d093247f01e3d6fcddd7bee4cad8fbf207ac08d08ada588b8771929cc0775`,
uses Boolean source digits and an aligned temporal rotation, then invokes the
finite-stencil mass bound. It does not assume a high-mask condition. The
client finally uses the partial transport residue and bounded block-sum
digits to identify that cyclic output with the physical `blk` digit.

This equality retains all raw stencil terms; it does not itself prove the
specific parity and decoder conditions at high-mask phases, complete packing,
graph zero, retained-byte binding, or an iPRA theorem. This is source-only
inspection, not a fresh Lean replay or authentication of the dependency
closure. The original author compile and its inherited provider limitations
are documented in the [prototype README](../../research/ordinary12-ipra-bridge/compact44-marked-physical-column-prototype/README.md).
