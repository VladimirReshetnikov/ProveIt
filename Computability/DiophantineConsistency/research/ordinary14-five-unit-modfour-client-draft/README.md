# Five-unit mod-four shape client — source draft

This draft composes the independently reviewed direct-first signed-pair
fact with existing `ArithmeticAdaptiveFactorUnits2011.main_bad`, `aux_bad`
and `strong_bad`. It takes the three exact `ZMod 4` residue-shape identities
as explicit premises and concludes that all five signed pairs equal +1 when
their product is one and `m≥2`. The fourth pair is the unrestricted guard.
All residue arguments can be arbitrary; no graph valuation, sign, port, or
external standard-integer interpretation is assumed.

For the 75/74 graphs the required residue identities have the forms of their
main, direct-y auxiliary, and strong factors, but this client does not prove
those graph identities or convert a literal `InternalZero` into the signed
product premise. Those bindings, `m≥2`, guard positivity, the 74↔75 model
map and provider compatibility remain separate. The imported five-unit draft
and this source have not been elaborated in Lean; no iPRA, byte or PDF claim
is made.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-five-unit-modfour-client-draft/check_source.py | cmp - research/ordinary14-five-unit-modfour-client-draft/observation.json
```

The finite controls exhaust the displayed modulo-four inputs; they do not
verify the Lean draft or establish a graph theorem.

Independent source review: [five-unit mod-four client](../../reviews/ordinary14-five-unit-modfour-client-independent/README.md).
