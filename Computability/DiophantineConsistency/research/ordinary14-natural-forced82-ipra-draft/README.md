# Natural 82 endpoint clients: source proposal

`Natural82Endpoint.lean` is an **unelaborated source-only proposal** for
transporting the existing natural-86 endpoint clients to the 82-row graph.
Its source checker pins and inspects the intended direct dependencies; it
does not run Lean or prove any client. The proposed graph transcription,
ring and model bridges, predecessor proof, natural-86 endpoint, and their
own source-only dependencies remain unelaborated. No end-to-end iPRA theorem,
physical coefficient-byte binding, PDF binding, or fresh provider replay is
established here.

The expression uses the existing symbolic port tuple
`CompactSymbolicModelIff.p`. Its first port is the integer cast of the
unexpanded natural `CompactFixedBeta.betaNat = 2^(67*8807)−1`. The draft
proposes a difference-ring equality between this port and the image of the
model's natural cast of that beta, and obtains positivity from the existing
`CompactFixedBeta.bounds`. Neither proposal equates the symbolic term with
external coefficient bytes.

The proposed `SameNoZero` comparison is between the literal natural-82
expression and `Natural86EndpointDraft.expression`. It uses
`Natural82ModelDraft.exists_zero_iff_of_predecessors` and discharges its
explicit predecessor premise with the **unelaborated**
`GraphPredecessors82Draft.predecessors_of_zero`, supplied with the beta
representation and positivity. The two zero witnesses generally differ in
three coordinates; no pointwise same-valuation zero equivalence is claimed.

The remaining source proposes a `PolynomialBridge` using the existing
natural-86 bridge, followed by native, standard, and equality-only reference
clients through the repository's existing adapters. These statements only
describe a proof route until the entire dependency chain is elaborated and
its hypotheses and axioms are audited; an `IΣ₁` model interface alone does
not demonstrate a derivation in iPRA. The inherited endpoint qualifications
and external physical binding obligations remain in force.
The five `#print axioms` commands in the source are intended for a future
build; no output from them has been obtained or audited.

An [independent source review](../../reviews/ordinary14-natural-forced82-ipra-independent/README.md)
checks the selected port facts, witness directions and adapter signatures;
it does not elaborate the endpoint.

```
python3 -I -S -B research/ordinary14-natural-forced82-ipra-draft/check_source.py > /tmp/natural82-ipra.json
cmp /tmp/natural82-ipra.json research/ordinary14-natural-forced82-ipra-draft/result.json
```
