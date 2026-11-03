# Compact44 base low-mask no-carry: source-only review

This source inspection covers
[`CompactBaseLowNoCarry.lean`](../../research/ordinary12-ipra-bridge/compact44-base-low-nocarry-prototype/CompactBaseLowNoCarry.lean)
at SHA-256 `367c769e67dfde9a27c3dbdd67f0a0cb28b2b753a70ebb92a0d6a3059f8e6bf6`.
No statement or hidden-premise issue was found in the inspected argument.

The theorem `base_noCarry` states, for an arbitrary element `a` of a model
of IΣ₁, that `packedCell a 0` has binary no-carry against
`CompactConcreteIncrement.mask` when `a ≠ 1`. It does **not** require
`a < 943`. Its mask is the exact symbolic finite-list mask defined by
[`CompactConcreteIncrement.lean`](../../research/ordinary12-ipra-bridge/compact44-concrete-increment-prototype/CompactConcreteIncrement.lean),
SHA-256 `91744fb88bf1f88da6c58d9311ae674ff28c2c9201e415d953a318cafe8976ac`;
the theorem alone does not identify that recipe with every retained literal
or document byte sequence.

The proof establishes that the cell's subdigits are Boolean and that each
nonzero subdigit lies at a supported position. A model position `k < 8807`
can be represented by a standard natural numeral via `eq_nat_of_lt_nat`;
the support argument then covers selectors, the dummy position, and the
finite copy-code lookup. For each supported position the symbolic mask
subdigit is even, hence disjoint from a subdigit of value one. The theorem
reconstructs the mask from its 8807 subdigits using its model size bound and
then applies represented-block no-carry to all subdigits. The packed cell
has dummy input fixed to zero; no general dummy value is claimed.

The inspected supporting workspace sources were
[`CompactCellDigitSupported.lean`](../../research/ordinary12-ipra-bridge/compact44-cell-support-prototype/CompactCellDigitSupported.lean),
SHA-256 `e8ac4b98a46fa38e3930e99d1d2e8dea4aefae4330f14d75b29257afa890f9ed`;
[`CompactCellSupport.lean`](../../research/ordinary12-ipra-bridge/compact44-cell-support-prototype/CompactCellSupport.lean),
SHA-256 `836d043325b895b7b9bf3ec703b98a8aa98b4de4cc8976f5e40eb19c62179494`;
and [`CompactPackedCell.lean`](../../research/ordinary12-ipra-bridge/compact44-cell-packed-prototype/CompactPackedCell.lean),
SHA-256 `dfd1515969f158ca39df561fe86f70c545d0e1e68c5d423767f927bd50e05e40`.

The result does not establish the special origin subtraction/increment
condition, product or high-mask conditions, a full packing, graph zero, or
an iPRA endpoint. This inspection does not replay Lean or authenticate the
full source/object closure, package, or dynamic-loading ancestry. The
separate author compile observation and inherited provider limitations are
described in the [prototype README](../../research/ordinary12-ipra-bridge/compact44-base-low-nocarry-prototype/README.md).
