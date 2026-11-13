# Natural 80 endpoint clients: source-only proposal

`Natural80Endpoint.lean` is an **unelaborated source-only proposal** for
transporting the natural-81 endpoint clients to the 80/107 graph. The
checker pins and inspects its direct source dependencies, selected symbolic
port references and seven axiom-print commands; it does not run Lean or
prove the clients. The entire new graph, factor, gamma-positivity,
gamma-shift, symbolic-port and natural-81 chain remains unelaborated. This
is not an end-to-end iPRA theorem, physical coefficient-byte or PDF
binding, or a fresh provider replay.

The expression uses the existing `CompactSymbolicModelIff.p` tuple. Its
ports are the integer casts of the four symbolic naturals

```
beta = CompactFixedBeta.betaNat,
K0   = paramKernel rho,
MC   = lowNat,
MF   = CompactFixedBeta.betaNat+highNat.
```

The source reuses the proposed symbolic beta and strict-K0 representation
lemmas and proposes representation lemmas for MC and MF. It invokes the
source-only `CompactPortBoundsSlimDraft.port_bounds` for `beta>0`,
`MC<beta`, and `MF<2*beta`, and the separate strict-K0 model draft for
`K0>0`. These symbolic declarations are not identified with external
coefficient bytes in this packet.

The proposed `SameNoZero` client composes the natural-80-to-81
gamma-shift zero-existence draft with those explicit model port witnesses.
The two zero witnesses generally differ in gamma, so no same-valuation
zero identity is claimed. The remaining source proposes a
`PolynomialBridge` from the natural-81 bridge, followed by native,
standard, and equality-only reference clients through repository adapters.

Each client is a proof route, not a theorem until the full dependency chain
elaborates and its hypotheses and axioms are audited. In particular, the
`IΣ₁` model interface alone does not demonstrate an iPRA derivation. The
seven included `#print axioms` commands have not been executed. Physical
coefficient, PDF, provider, and inherited endpoint qualifications remain
separate obligations.

An [independent source review](../../reviews/ordinary14-natural-forced-gamma80-ipra-independent/README.md)
checks the selected port assumptions, zero-map directions and endpoint
signatures without elaborating the client or running its axiom reports.

```
python3 -I -S -B research/ordinary14-natural-forced-gamma80-ipra-draft/check_source.py > /tmp/natural80-ipra.json
cmp /tmp/natural80-ipra.json research/ordinary14-natural-forced-gamma80-ipra-draft/result.json
```
