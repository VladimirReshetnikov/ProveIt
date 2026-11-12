# Eta-natural positive C and compact rank: model drafts

These source-only proposals are **not Lean-elaborated**. They use the exact
eta-natural prototype and its proposed signed-factor bridge, and inherit all
model/provider/axiom limitations. They do not prove an eta-zero contradiction
or an iPRA endpoint.

The graph has `F=v1+1`, `alpha=v2+1`, `b=J*beta`, `q=1+b`,
`X=q*v6`, `k=v9+v10+1`, `m=X*Y²`, `ell=m*k`, and
`Bt=(q−F−alpha)*(X+K0)−F`, with all subtractions in the difference ring.
Assume positive b and natural K0. If `C=q−F−alpha≤0`, then `Bt<0`. The
actual first carrier is

```
Z=b*(ell+k+r−k*Bt)−Bt,   r=v8≥0.
```

It follows that `Z>b*(ell+k)≥0`, even for the previously awkward boundary
`k=1, r=0`. Also

```
(ell+k)² − (1+m*(m+1)*k²) = ell*k + k² − 1 ≥ 0
```

because `k≥1`. Therefore `Z²>b²*(1+m*(m+1)*k²)`, contradicting the
prototype's own first signed norm. This needs neither positive eta nor
positive r or X. The graph-level `gap` obtains positive J from the separate
prototype J client and takes positive model-cast beta explicitly.

The natural rank uses the old arithmetic expression
`((q−1)*(q−F)+alpha)*(q²−1)+(MC+q*MF)*J`, with *model-natural* subtractions.
Only after obtaining `F≤q` does `rank_representation` propose its equality
with the exact prototype `EtaNaturalXPositiveDraft.rankRing`; the earlier
source `Residue90GraphNormsDraft.rank_representation` is used only as a
fact-level arithmetic equality with matching q/F/rank definitions, never as
a graph-zero theorem. The compact client uses the prototype graph zero, the
compact symbolic natural tuple, the fixed beta/mask bound theorem, and the
separate compact rank-window client. The proof leaves K an arbitrary natural;
the retained kernel choice, fixed external byte/PDF associations, and source
provider authentication remain open. This bound alone gives the displayed
window, not all later hypotheses such as R≥26 or the early-index witness.

`first_norm` and all graph/tactic reduction, positivity, `rank_representation`,
and compact-port casts must still be checked by Lean with compatible
providers. The factor-unit bridge, separate J proof, exact graph/fixed-port
bindings, eta-zero graph maps and internal endpoint are not established here.
The proof does not use abstract-model `omega`.

Run `python3 -I -S -B research/ordinary13-eta-natural-gap-rank-model-draft/check.py`
from `Computability/DiophantineConsistency` and compare with `receipt.json`.
The checker validates source signatures and bounded exact graph/rank and
scalar inequalities, not a model proof.
