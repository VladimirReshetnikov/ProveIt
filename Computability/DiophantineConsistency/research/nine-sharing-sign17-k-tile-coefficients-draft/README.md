# K tile coefficient literal blocks: source-only drafts

The isolated generator checks the pinned external coefficient array and
candidate-weight witness, then emits 16 proposed Lean modules comparing each
doubled in-Lean weight block with a literal coefficient block. Sizes are 32,
fourteen 64-entry blocks and a 14-entry tail, covering candidate positions
0–941. Each proposed proof is a bounded finite case check. The external
array comparison is a Python observation; no Lean filesystem/JSON or file
binding follows from generated source. The 44 control positions and separate
sentinels are handled elsewhere.

These modules passed a [guarded Lean run and independent terminal audit](../nine-sharing-sign17-k-tile-coefficients-check/README.md).
The checked block theorems still require a checked union and a
separate binding to the external array representation. Generator SHA-256:
`06abf545d90cb13ce7d9e6ace79b0d353576e10bda973dee8d3b034c8e526546`.
