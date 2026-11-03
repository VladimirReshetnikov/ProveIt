# Compact44 all-phase high-mask theorem: source-only review

This inspection covers
[`CompactMarkedAllHigh.lean`](../../research/ordinary12-ipra-bridge/compact44-marked-all-high-prototype/CompactMarkedAllHigh.lean),
SHA-256 `db7cd6327fe6faf7be1867f3e95a0a94f50cce85e4365c3db4e6675d488c881b`.
No omitted high-mask phase or additional premise was found in the inspected
assembly and immediate supporting statements.

The theorem assumes a model of IΣ₁, Σ₁-definable `row` and `dummy`, a
`CompactWord row N s`, `1 < N`, `s < N`, and `dummy j ≤ 1` for **all** model
indices. For each `j<N` it concludes binary `NoCarry` between the physical
normalized `blk` of the normalized cell word and the exact symbolic
finite-list `highNat`. It does not assume that full high-mask condition.

The source invokes the separately proved phase reduction, supplies its block
size from the marked cell-sum theorem, and supplies padding zeros through
the marked padding theorem. Below 8792 the `active` predicate enumerates:

| Phases | Supporting local check |
| --- | --- |
| 0 | phase-zero `NoCarry` |
| 1013–1022 | vertical fields and marker |
| 1065–1073 | horizontal fields and marker |
| 2195 and 3296 | distant anchor checks |
| 4393 and 5495 | target checks |

The phase-reduction theorem handles every other phase below 8792 by proving
the symbolic mask subdigit is zero. For the padding branch it requires
`p<8807` and `8792≤p`; the imported `marked_padding` proves a zero block
subdigit for **all** `p≥8792`, so it covers phase **8806** as well as
8792–8805. The underlying explicit high-digit list actually ends with a
zero at 8806; the assembly does not depend on omitting this position.
The exact list is in
[`CompactHighPopulation.lean`](../../research/ordinary12-ipra-bridge/compact44-high-population-prototype/CompactHighPopulation.lean),
SHA-256 `b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d`.

The inspected phase reduction source has SHA-256
`db7192c7ffef36d31eda3425554c7250f3ffd1da6b30ac5af0369c7a9f7d932c`,
the marked-padding source
`2a6a63c512f364b0a6b9e1bfaeaeb046aee4ec69851d25a8d710b1258dbe8c99`,
the field/marker interval source
`781d84ba0b495b78e333887410075278eda606f5ec30b3c3e6def5d41bb99409`,
and the phase-zero source
`6903c6f89d5c2e3cae70a724a82f6e11b3cc9decff907ca8e8cb8e8b75cb2d4c`.

This is a source-only inspection, not a fresh Lean replay or a complete
source/object closure or provider audit. The separate single-author mixed
provider compilation and its inherited transitive, package and dynamic
ancestry limitations are recorded in the theorem's observation packet. This
ordinary high-mask result alone does not supply the special decremented
origin mask, a complete packing, a graph zero, retained-byte binding, or an
iPRA theorem.
