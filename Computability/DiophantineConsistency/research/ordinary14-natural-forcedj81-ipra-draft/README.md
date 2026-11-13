# Natural 81 endpoint clients: source proposal

`Natural81Endpoint.lean` is an **unelaborated source-only proposal** for
transporting the natural-82 endpoint clients to the 81-row graph. The
checker pins and inspects its intended direct dependencies; it does not run
Lean or prove any client. The proposed graph transcription, J-shift model
bridge, symbolic K0 proof, natural-82 endpoint, and their own source-only
dependencies remain unelaborated. This is not an end-to-end iPRA theorem,
physical coefficient-byte or PDF binding, or a fresh provider replay.

The proposed `SameNoZero` comparison is between the literal natural-81
expression at `CompactSymbolicModelIff.p` and the natural-82 expression at
the same symbolic ports. The imported J-shift model draft supplies its
zero-existence equivalence subject to a represented, positive K0 model
element. The imported strict-K0 draft proposes both the representation of
symbolic slot 1 by `(paramKernel rho : V)` and its positivity; no physical
coefficient-byte equality is assumed or shown. The zero witnesses in the two
graphs differ in slot 0, so no pointwise same-valuation identity is claimed.

The remaining source proposes a `PolynomialBridge` using the natural-82
bridge, followed by native, standard, and equality-only reference clients
through existing repository adapters. These statements describe a proof
route until the whole dependency chain is elaborated and its hypotheses and
axioms are audited; an `IΣ₁` model interface alone does not demonstrate an
iPRA derivation. All inherited endpoint and physical binding qualifications
remain in force.

An [independent source review](../../reviews/ordinary14-natural-forcedj81-ipra-independent/README.md)
checks the stated port assumptions, witness directions and client signatures;
it does not elaborate the declarations or execute their axiom reports.

The source includes `#print axioms` commands for `sameNoZero`,
`polynomialBridge`, and the three endpoint declarations. They have not been
executed and do not yet provide an axiom audit.

```
python3 -I -S -B research/ordinary14-natural-forcedj81-ipra-draft/check_source.py > /tmp/natural81-ipra.json
cmp /tmp/natural81-ipra.json research/ordinary14-natural-forcedj81-ipra-draft/result.json
```
