# Compact44 origin low-mask no-carry: source-only review

This inspection covers
[`CompactOriginLowNoCarry.lean`](../../research/ordinary12-ipra-bridge/compact44-origin-low-nocarry-prototype/CompactOriginLowNoCarry.lean),
SHA-256 `dc932b5ba9ba1a1bc78db4fa076cbe63ea18767e6a37ec4d8d5a7bcfa9fedac3`.
No statement or missing-premise issue was found in the inspected proof.

The general `swap_origin_bit` lemma takes `NoCarry x m`, `x % 2 = 1` and
`m % 2 = 0`. Binary division decomposes `x` into `2*(x/2)+1` and `m` into
`2*(m/2)`. The first equation ensures `x ≥ 1`, so model truncated subtraction
gives `x-1 = 2*(x/2)`. Exchanging the two lowest bits leaves the common
higher-bit no-carry condition intact and yields `NoCarry (x-1) (m+1)`.

The specialization obtains the low bit one from the row-zero selector of
`packedCell 0 0`. The exact symbolic finite-list low mask has low bit zero:
position zero is in its support, so its corresponding mask subdigit is
even. Together with the separately proved base no-carry theorem, this gives
exactly `NoCarry (packedCell 0 0 - 1) (mask + 1)`. The theorem does not
assert this property for an arbitrary row or arbitrary initial dummy input.
Identifying the symbolic mask with retained literal or document bytes remains
a separate boundary.

This is a source inspection, not a Lean replay or a source/object closure
audit. It does not construct the marked origin or prove product, high-mask,
graph-zero or iPRA obligations. The independent base theorem's exact scope is
described in the [base source review](../compact44-base-low-nocarry-source-review/README.md);
the origin client's author-side compilation and inherited provider
limitations are described in its
[prototype README](../../research/ordinary12-ipra-bridge/compact44-origin-low-nocarry-prototype/README.md).
