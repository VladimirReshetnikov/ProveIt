# Independent review: prototype strong/auxiliary graph interfaces

The proposed graph strong and auxiliary fields match the pinned prototype and
the fact-level adapter at the source-interface level. No mismatched tuple,
signed rank, shifted coordinate or eta-positive premise was found. These are
unelaborated source proposals, not Lean-verified graph-zero consequences.

The strong path identifies graph `f=v3`, `I=c²*(v4+1)` and the natural Delta,
then takes the third equation of the same graph's `signed_norms` output.
The fact-level reflection receives precisely that signed equation and
returns its stated natural strong equation. No signed/natural rank equality
is needed for this strong step.

The auxiliary path takes the fourth signed-norm equation. Its field ordinate
uses the graph's signed rank; replacing it by the model-natural rank is
conditional on the exact `F≤q` premise of the separately proposed
`rank_representation`. Under that premise it has the signed form
`ι(f²*T*c)−ι(f²*R+c)` with the **same** rank R, `T=v5+1`, f and c. The
client then passes the resulting equation to the fact-level strict-bound and
positive-offset interfaces. Its geometry premises `c>1`, `Delta>0` and
`Delta<c³` are explicit; graph-zero geometry and shared witnesses must be
proved separately. Neither positive y nor positive eta is assumed.

The existing compact parity boundary's explicit strong and auxiliary
premises use `c=Y*k`. At `v9=0`, the prototype c is `v9+Y*k`, so those
forms have the correct proposed specialization. Supplying the raw signed
strong equation needs the same graph's `signed_norms` and f/I/Delta field
bindings; supplying the raw auxiliary equation needs `direct_auxiliary`,
the same valuation and port tuple, and `F≤q`. Both still require the
eta-zero normalization and actual Lean checking. This review does not claim
that either premise has already been removed from the compact boundary.

Run from this directory:

```
python3 -I -S -B check.py > /tmp/eta-graph-strong-aux-parity-independent.json
cmp result.json /tmp/eta-graph-strong-aux-parity-independent.json
```

The receipt pins the key source declarations and checks 300 bounded graph
field cases, including eta zero. These checks do not establish all-model
casts, graph factor units, a zero map, provider closure or an iPRA endpoint.
No reviewed source was modified.
