# Eta-natural strong and auxiliary: conditional fact-level adapter

This packet provides an **unelaborated source-only** fact-level route from the
prototype's proposed signed strong/auxiliary equations to the two hypotheses
of `EtaZeroIndexParityDraft.eta_zero_contradiction`. It does not evaluate the
prototype or prove its graph zero maps. All parameters in the client are model
naturals; `DiffRing V` carries the signed ordinate. The checker pins source
interfaces and selected graph rows and checks the ring identities. It does not
compile Lean or certify a model theorem.

For the prototype write

```
i = n_i+1, f=n_f, T=n_T+1, c=n_eta+Y*k,
Delta=(3+4a)+a², Q=Delta*(f²−1),
z=f²*(T*c−R)−c, A=f²*(T*c), B=f²*R+c.
```

Its separately proposed `EtaNaturalUnitBridgeDraft.signed_norms` exports
`(c²*i)²=Q` and `y²−Q*(y²−z²)=1`, with all quantities evaluated in the
difference ring. These equalities require graph zero and the separately
unelaborated unit-factor proof. The present module **assumes** their exact
natural representations; integer port casts, the signed rank versus its
natural truncated expression, and selected model parameters remain to be
bound to the actual graph.

The proposed `ordinary_strong_of_signed` reflects the first equality through
the injective natural embedding to

```
(i*c*c)² + Delta = Delta*f².
```

With `Delta>0`, `f_positive_of_strong` excludes `f=0` from this natural
identity. The strict-bound client assumes `c>1`, `i≥1`, `0<Delta<c³`, and
the natural strong identity; it binds `z=A−B` and `z+c=f²*(T*c−R)` and
applies `AuxOffsetFactsDraft.aux_strict_bounds` to propose `Q>1` and `z²>1`.
The shifted graph input gives `i≥1` after the graph binding.

Under the strict bounds, direct signed auxiliary equation, and `f>0`, the
proposed `index_aux_of_direct` obtains a positive natural `u` with
`z+ιu=ιy` via `AuxOffsetFactsDraft.positive_offset_of_direct`. It converts
both signed squares using `P72Root.ι_magnitude_sq`, reflects
`Delta*(f²−1)` using `P72Root.ι_tsub` and the derived `1≤f²`, and returns
precisely the natural absdiff equation required by the eta-zero contradiction:
`Delta*(f²−1)*absdiff(A,B)² + absdiff(A+u,B)² =
1+Delta*(f²−1)*absdiff(A+u,B)²`. The theorem does not assume `y>0` or `u>0`;
`u>0` is a proposed output.

A possible route to the required geometry is the separately unelaborated
`EtaNaturalNormLargeKDraft.large_first_ordinate`, followed by
`AuxGeometryEtaNaturalDraft.geometry_of_large_k`, with graph-bound `X,Y>0`,
`zeta=n_zeta+1>0`, natural first and main norms, and
`(X*Y+Y+2)²=Delta+1`. Those interfaces permit `eta=0`; the old
`AuxNormsToBoundsDraft` requires eta-positive and cannot simply be reused.
The geometry, factor-to-natural norm bridge, `X` positivity, and their exact
common witnesses are not supplied here. Other exact-index inputs—early first
Pell index, `R≥26`, rank window/congruence, main norm/index, positive q and
model port casts—also remain separate. The fact client imports `AuxOffsetFacts`,
whose research providers include `AuxRootBounds`, `AuxRootBridge`, and its
own `FirstRootBridge` dependency. No compatible provider closure, axioms,
Lean build, physical PDF association, or internal-iPRA theorem is claimed.

From `Computability/DiophantineConsistency`, reproduce the read-only receipt:

```
python3 -I -S -B research/ordinary13-eta-natural-strong-aux-adapter-draft/check.py | cmp - research/ordinary13-eta-natural-strong-aux-adapter-draft/receipt.json
```
