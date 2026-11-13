# Independent source review: eta-natural auxiliary drafts

The generated geometry theorem's signature and body match the pinned original exactly after removing only eta positivity and replacing the last strict `Y*k<eta+Y*k` by the natural non-strict inequality. The preceding comparison `A<Y*k` is already strict, so the conclusions `A<c`, `1<c`, `0<Delta<c³` remain mathematically valid at eta=0 under the unchanged positive-Y, large-k and discriminant hypotheses.

The separate signed fact client explicitly assumes `1<c`, `1<=i`, `0<Delta<c³`, the exact strong norm, the signed identity `z+c=f²*t`, and `Q=(i*c²)²`. Its calls to the earlier proposed strong-gap and signed-discreteness lemmas have the correct direction and yield `Q>1` and `z²>1`. The positive-offset theorem then assumes those strict bounds and the direct auxiliary equation with model-natural y; from the square comparison it first derives y>0, then z<y, and obtains positive natural u representing y-z. Neither y positivity nor eta positivity is an input to this second theorem.

The imported `AuxRootBounds` and `AuxRootBridge` names refer to separate unelaborated research drafts; `AuxRootBridge` itself imports `FirstRootBridge`. No compatible compiled provider closure is established here. The large-k inequality, graph factor units, exact signed/strong identities, model cast bindings and relation to an eta-unshifted equation remain explicit obligations. Both source receipts reproduce; no Lean, axiom report, reduction or iPRA theorem is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-natural-auxiliary-independent/check.py | cmp - reviews/ordinary13-eta-natural-auxiliary-independent/result.json
python3 -I -S -B research/ordinary13-eta-natural-auxiliary-draft/generate_geometry.py | cmp - research/ordinary13-eta-natural-auxiliary-draft/geometry-result.json
python3 -I -S -B research/ordinary13-eta-natural-auxiliary-draft/check.py | cmp - research/ordinary13-eta-natural-auxiliary-draft/facts-result.json
```
