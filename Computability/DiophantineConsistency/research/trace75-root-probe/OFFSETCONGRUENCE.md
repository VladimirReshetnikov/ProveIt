# Trace75 natural offset congruence

`Trace75OffsetCongruence.graph_offset_congruence` proves in any IΣ₁ model
that `k % q⁴ = (rankNat + 1) % q⁴` for a positive trace75 zero, provided the
model has β≥31, `MC<β`, and `MF<2β`. The remaining port `K0` is arbitrary.
The proof first uses the exact graph rank's natural cast and the signed
offset-divisibility theorem, then applies a generic lemma converting
divisibility in the difference ring to equality of natural remainders. It
does not establish an equality of indices or a halt/iPRA equivalence.

`run-offsetcongruence.py`, `observations/offsetcongruence-attempt01/`:
Lean exit 0, no warning/error, object
`/tmp/trace75-offsetcongruence-_fmdaxmm/Trace75OffsetCongruence.olean`,
SHA-256 `68f62881983fd6457780b66ebe12e38ae8613e177cac4f5f987a59dfe94808d3`.
The source's draft comment predates this accepted check. Direct provider
pins and the selected search path are recorded; historical transitive and
package ancestry and external graph/file binding remain inherited limits.
