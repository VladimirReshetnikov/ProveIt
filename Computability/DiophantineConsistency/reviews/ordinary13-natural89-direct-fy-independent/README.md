# Independent source review: natural 89 f/y positivity

The pinned `research/ordinary13-natural89-direct-fy-model-draft/` is an
unelaborated source proposal for the `DirectFY K` cut. Its own checker
reproduces. The independent receipt checks the exact 89→88→87→86→85 row
substitutions, coordinate preservation and 546 bounded signed-divisor
identities. Run `python3 -I -S -B check.py | cmp - receipt.json` from this
directory. These checks do not establish the graph maps or arithmetic in
Lean or authenticate providers.

In the prototype client, all ports are integer casts of the explicitly
natural tuple `p`. The natural discriminant is `(3+4a)+a²≥3`, with a
natural a. The graph's signed strong factor is reflected by the separate
graph-strong client to `(i*c*c)²+Delta=Delta*f²`; the cited fact-level
`f_positive_of_strong` then rules out f=0 using `Delta>0`. The f client does
not require a natural rank representation, positive eta, beta or X.

For y, the source correctly uses the actual graph's raw signed auxiliary
ordinate z, without identifying it with a natural-rank expression. At y=0,
its equation is

```
0 − Delta*(f²−1)*(0−z²) = 1.
```

Thus the displayed difference-ring witness `(f²−1)*z²` gives
`1=Delta*((f²−1)*z²)`, exactly the orientation used for signed
`Delta ∣ 1`; the source's `linear_combination -haux` has the correct sign.
The cited `Trace75IntegralTransport.natural_dvd_of_signed` takes represented
model naturals `Delta` and `1` and reflects that divisibility to the natural
model. Its positive-dividend bound would give `Delta≤1`, contrary to
`Delta≥3`. No positivity of f or y, eta, beta or the signed ordinate is
used by this branch. The current theorem quantifies a natural **whole port
tuple**; it does not claim the same interface for arbitrary integer ports.
The generic unit-factor proof it imports is itself conditional on the exact
prototype and remains unelaborated.

The four source maps send an 89 valuation forward by incrementing J=0,
gamma=12, w=6 and eta=9, in that order, to the exact 85 prototype. Both
f=3 and y=11 are unchanged. The checker verifies the corresponding four
literal row substitutions; the proposed Lean `zero_iff` and final `simp`
still need elaboration. The resulting theorem has exactly the all-model
`Natural89Positive80TransportDraft.DirectFY K` type for the compact natural
`ports K`, with arbitrary natural K. It does not prove the independent
`RReplacement K`, claim the original r is positive, or provide the positive
80 parent bridge.

No concrete sign, tuple, or direction mismatch was found in these inspected
interfaces. All factor-unit proofs, signed quotient reflection, exact graph
evaluation, source/provider/axiom closure, fixed byte/PDF provenance and
internal-iPRA endpoint remain separate and unverified here.
