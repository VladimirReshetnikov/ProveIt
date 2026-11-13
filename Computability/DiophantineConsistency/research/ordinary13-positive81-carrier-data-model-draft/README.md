# Positive-81 carrier root construction, source draft

This packet proposes the forward first-residual witness from the exact positive
81 graph to the positive 83 graph at the compact tuple. It also records a
conditional reverse companion-carrier lemma. **No Lean elaboration, provider
replay, complete `CrossRootCut`, parent `PolynomialBridge`, iPRA equivalence,
or PDF connection is established.** Every imported graph, calibration and
arithmetic source remains subject to its own unelaborated/provider obligations.

For a positive 81 valuation, write `b=J*beta`, `q=1+b`,
`C=q-F-alpha`, `X=q*w`, `Y=q^3*s`, `ell=X*Y^2*(eta+zeta)`, and
`k=eta+zeta`. The exact first carriers are

```
P = C*(X+K0)-F
Q = C*(X+K0*q)-F*q
Q-P = b*(C*K0-F).
```

The first residual is `Z(P,r)^2-b^2*(1+ell*(ell+k))`, where
`Z(P,r)=b*(ell+k+r-k*P)-P`. `PositiveCarrierData.lean.src` generalizes the
previous zero-r source extraction to arbitrary natural r: it proposes deriving
`P>0`, `b | P`, and a common natural norm root `tau>ell`. The proof relies
on signed-magnitude extraction, model square divisibility, and reflection
from signed to natural divisibility. All of these are source-level proposals.

`CompanionCarrierFacts.lean.src` derives `Q>0` from `C>=1`, `F+2<=q`,
`q>0` and `q^2<=X`, and transfers signed divisibility. Given those facts,
it proposes the positive target branch
`r'=k*(Q-1)+Q/b+(tau-ell)` and exact first-norm equality, using natural
quotient witnesses rather than model division. Its separate reverse lemma
shows positivity and divisibility of P from Q when C and X are strictly
positive; it does **not** extract C>0 from an 83 graph zero.

`Positive81ForwardCarrier.lean.src` binds the expressions to the actual
81/83 first graph residuals; beta positivity, the graph gap, and `q^2<=X`
are explicit arguments. `Positive81ForwardCompact.lean.src` proposes to
supply them using the actual 81→85 forward image, compact beta and gap
sources, and `Positive81ExactMainDraft.calibration81_original`. The latter
has a substantial unelaborated chain of exact-index, same-witness, model
arithmetic and provider obligations: this file does not independently prove
or validate that chain. The wrapper produces only the forward *first residual*
witness, not either complete graph zero by itself.

For the reverse half of `CrossRootCut`, a graph-specific 83 first-norm
binding, extraction of represented C>0 and X>0 from that very graph, and
construction of the positive 81 root remain to be supplied and checked.
The unconditional direction and all all-model graph-field identities are
not established by the finite checks below.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive81-carrier-data-model-draft/check.py
```

The checker pins the draft and direct source inputs, inspects the changed
81/83 carrier rows and shared rows, and tests bounded scalar companion and
positive-branch arithmetic. These finite checks are not proofs in an
arbitrary model and do not check Lean syntax, tactics, dependencies, axioms,
resource constraints, or endpoint provenance. `receipt.json` is its output.
