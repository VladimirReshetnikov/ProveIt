# Independent review: positive 84 rank window

The pinned 84 graph's first carrier is exactly `P=(q-F-alpha)*(X+K0*q)-F*q`; the graph root and first norm have the arguments required by the proposed `P_positive` interface, including the same natural root-coordinate `v 8`, `b=J*beta>0`, and `k=eta+zeta≥2`. If `P>0`, natural nonnegativity of `X`, `K0`, `q` and `F` gives `F+alpha<q`: otherwise the product is nonpositive and so is P. This argument does not assume a sign for the graph root, `q ∣ X`, or a zero of the 83 graph.

The gap supplies `F≤q`, while `q≥1` supplies `q²≥1`; these are the source's explicit hypotheses for casting the truncated subtractions in `rank_representation`. The actual graph rows and the proposed natural rank agree in form:

```
R=((q-1)*(q-F)+alpha)*(q²-1)+(MC+q*MF)*J.
```

For the compact tuple, the existing port definition is `![beta,K,low,beta+high]`; its fourth entry is used once as `MF=beta+high`, with no additional beta shift. The draft invokes the existing compact-window theorem with the actual positive-gap hypothesis. The separate lower bound uses positive alpha and `q≥6`; the compact beta and positive J source interface supplies the stronger `q≥46`. The final window cut supplies the lower bound and window only. It does not independently provide the signed rank congruence: the early/exact composition derives that from the still-explicit same-main/strong/aux graph cut.

The review pins the actual graph, source interfaces, compact definitions and author receipt. Its checker verifies critical rows and signatures and reproduces the author check. Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-rank-window-carrier-independent/check.py | cmp - reviews/ordinary13-positive84-rank-window-carrier-independent/receipt.json
```

This is a bounded source-level review, not Lean elaboration. The proposed graph and model proofs, casts, ordered-model tactics, provider closure, main/strong/aux witness extraction, iPRA endpoint and PDF binding remain open.
