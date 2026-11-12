# Independent audit: eta-zero auxiliary offset

The proposed inequalities and positive offset follow in the intended discretely ordered difference ring **if the stated natural norms, signed identities and large-k bound are supplied**. They do not use eta positivity or the desired graph zero map. The reasoning is finite ordered-ring arithmetic with natural-cone reflection, so it does not rely on enumerating standard indices; its application to an actual eta-unshifted graph remains unproved.

Write `M=X*Y²`, `A=X*Y+Y+2`, `c=Y*k`, and `A²=Delta+1`, with X,Y,i positive model naturals and `k>=8M+4`. Since `Y>=1`, `M>=X` and hence `k>=X+4`. Therefore

```text
c = Y*k >= Y*(X+4) > X*Y+Y+2 = A >= 2.
```

The strict step uses `3Y>2`, not eta>0. Thus `c>1`, `Delta>0` and `Delta<A²<c²<=c³`. The existing unelaborated `AuxGeometry.geometry_of_large_k` source assumes eta>0 and uses it in its last strict step; a generalized proof must replace that step by the non-strict `Y*k<=eta+Y*k` after the already strict earlier bound.

Let `I=i*c²`, `F=f²`, and take the strong identity in additive form `I²+Delta=Delta*F`. Positivity of i gives `I²>=c⁴`. If `F<=c+1`, then `I²<=Delta*c<c⁴`, contradiction; hence `f²>c+1`. In the signed difference ring, assume `V+c=f²*t`, where `t=T*c-R` may have either sign. If `V²<=1`, ordered-ring square comparisons give `-1<=V<=1`, hence `0<V+c<f²`. This makes t positive; the pinned `ModelDifferenceRing.one_le_of_pos` supplies `t>=1`, contradicting `V+c<f²`. Therefore `V²>1`. Also `Q=I²>1` follows from i>=1 and c>1.

For natural y, the stated auxiliary identity `(Q-1)*(y²-V²)=V²-1` now implies `y²>V²` since `Q-1>0` and `V²-1>0`. The natural y is nonnegative, so y exceeds the natural magnitude of V and in particular `ι y-V>0`. The difference-ring natural-cone representation supplies a model-natural u>0 with `ι u=ι y-V`; consequently `V+ι u=ι y`. The `absdiff`/signed-ordinate conversion and the exact `P72Exact` auxiliary equation must still be bound to the particular graph. The source-only `AuxRootBridge.square_gt_of_aux` and `above_of_positive` are relevant fact-level interfaces; its full five-squares equivalence is not automatically a theorem for the pinned product graph.

## Obtaining large k without circularity

The unelaborated `AuxRootBounds.first_ordinate_large` explicitly needs M>0, k>2 and the natural first-Pell norm; it cannot be applied from k>0 alone. If those facts and the natural main norm have been obtained independently, the k=1 first-norm exclusion and k=2 main-norm exclusion are possible routes. At eta=0 and k=2, `c=2Y`; with Y>0, `1<c<2A`, and the separate unelaborated fact-level `ModelMainSquareGapDraft.no_main_square` rules out `d²=1+Delta*c²`. The bundled `two_ordinate_impossible` is **not** directly applicable: it assumes eta>0 and zeta>0, derives eta=zeta=1, and uses `c=2Y+1`. A new eta-zero specialization of the generic square gap and a natural-norm binding are required.

The current 86-operation graph still computes `eta=n_eta+1` and uses a product of four factors, with output `P0123-1`. This audit has not defined or checked an eta-unshifted graph. A proposed graph-zero client must first establish the relevant factor units and their signs in every intended model, extract the first/main/strong/auxiliary equations and all positive/represented parameters, and prove the required rank, casts and Pell witnesses without assuming the desired eta-zero contradiction or a zero-existence map. The sign arguments, compact port/provider bindings, internal parity/index theorem and endpoint are separate obligations. In particular, the finite examples below do not discharge a product-factor sign or any full-zero implication.

The checker pins the source interfaces and shifted graph, tests bounded algebraic instances and the k=2 square gap, and verifies a signed auxiliary control. The original route audit's receipt reproduces. No Lean, model-provider replay, new graph or equation reduction is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-zero-auxiliary-independent/check.py | cmp - reviews/ordinary13-eta-zero-auxiliary-independent/result.json
python3 -I -S -B research/ordinary13-eta-zero-index-route-audit/check.py | cmp - research/ordinary13-eta-zero-index-route-audit/result.json
```
