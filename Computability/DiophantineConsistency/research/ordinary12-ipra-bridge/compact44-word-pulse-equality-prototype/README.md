# Explicit pulses in the represented compact word

`CompactWordPulseEquality.lean` specializes the exact normalized-cell pulse
identity to each cell of the constructed word. For any model row and dummy
functions it proves `cellWord row dummy j` equals the zero-dummy cell plus
`2^(67*1063) * (dummy j % 2)`; if that dummy value is at most one, the
modulo can be removed. It also identifies the entire represented outer word
as the block sum of those explicit pulsed cells.

This is the missing equality between the cell family used in the packed-word
and temporal-carry clients and the pointwise pulse used in the conditional
packing/rank clients. It does not establish pulse support, product/high-mask
conditions, graph zero or an iPRA proof.

The guarded single-author compile exited 0 without warnings or `sorryAx`,
with unchanged sampled direct dependency and companion guards. Its three
named axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
The first run briefly overlapped another Lean compile because of coordination
latency. A second bounded run in an available Lean slot also exited 0 with
unchanged sampled guards and produced the same object hash; both observations
are retained. Provider package, transitive, dynamic and between-observation
ancestry remains inherited; `/tmp` paths may disappear.
