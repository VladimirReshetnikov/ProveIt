# Source-only C-fold witness algebra

These are **unelaborated Lean source proposals**, with no provider selection, graph evaluator theorem, all-model bridge, or iPRA endpoint. They isolate exact algebra and positive-coordinate cuts shared by the current2011 [88/28 C-fold](../adaptive87-current-cfold88-degree28/README.md) and its [88/30 parent](../adaptive87-four-square-current88-30/README.md). The checker pins both entire literal graphs, verifies their exact one-row difference, checks the root/residual row shapes and verifies the free-ring identities below. It does not establish that the Lean definitions evaluate the graphs.

`CfoldWitnessAlgebra.lean.src` defines the two fact-level roots and four-square output over an arbitrary commutative ring. It proposes:

* `root_transport` and `sphere_transport`: the substitution `r_old=rho+k*(Bt−C)` makes the first roots, and then the complete sphere values with the same other three residuals, equal.
* `root_transport_inverse`: the inverse direct substitution `rho=r_old−k*(Bt−C)` is an exact ring identity, with **no** positivity claim.
* `switch_root`: assuming `M=q3*b`, `Y=q3*s` and `Bt=b*t`, the switched coordinate `rho=(C−1)*k+(tau−ell)−s+t` gives child root `M*tau`.
* `bt_gap`: under `q>=2`, `C>=1`, `X>=q²`, `K>=0`, and `F<=q−2`, derive `Bt−C>=2q−1` when `Bt=C*(X+K*q)−F*q`. These are explicit ordered-ring hypotheses, not facts extracted from a graph zero here.
* `transported_positive` and `switch_positive`: positive-coordinate cuts under their displayed inequalities, including the explicit switched-root gap `s<tau−ell`.

`CfoldWitnessRepresentatives.lean.src` proposes two wrappers for a model `V` of IΣ₁ and its difference ring. `direct_coordinate` assumes the signed-ring comparison `C<=Bt` and uses the existing prospective `positive_as_successor` interface to represent `ι(rho+1)+ι(k)*(Bt−C)` as `ι(n+1)`. `switched_coordinate` does the same for the switched expression under the explicit `C>=1`, `k>=0`, `s<tau−ell`, and `t>=0` ring hypotheses. The first coordinate `rho+1` models the existing positive shift; no natural truncating subtraction is hidden. The imported `PositiveGapRepresentation` is the pinned source-only helper, not an authenticated compiled provider.

To connect these cuts to the real 88/28 and 88/30 equations, a future proof must construct or select exact Lean literals for both graphs; bind `M`, `ell`, `k`, `C`, `Bt`, `Y`, `b`, `q3`, the unchanged residuals and the high port at one valuation; prove the `Fin 13` coordinate-8 successor update and whole-output evaluations; and derive the ordered hypotheses in every intended model. In particular, the direct map needs the model version of Cal and the actual `Bt−C` extraction; the switched map needs the parent first-root quotient, divisibility and Pell-gap witnesses. Neither direction follows from a finite numerical test or the source-only ring theorem alone. The standard-integer Cal replay and independently reviewed witness maps have their own scope and are not imported as model theorems.

From the DiophantineConsistency directory:

```sh
python3 research/adaptive87-current-cfold-witness-algebra-draft/check.py > /tmp/adaptive87-cfold-witness-current.json
cmp research/adaptive87-current-cfold-witness-algebra-draft/result.json /tmp/adaptive87-cfold-witness-current.json
```

The check confirms the exact free-ring forward, inverse and switched-root identities, pins the source interfaces and graph rows, and exercises bounded order controls. Those controls do not establish the proposed Lean tactics, source elaboration or universal model statements. No Lean/build/staging was performed and no existing packet was changed.
