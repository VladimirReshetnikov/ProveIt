# Independent source review: f and y positivity

The draft uses the correct residual indices: 3 is the strong residual `I²-Delta*(f²-1)`, while 2 is the auxiliary residual `y²-Q*(y²-V²)-1`. The graph's ordinate is signed and includes the actual signed R; the pinned magnitude theorem represents its square by a nonnegative model element without assuming the ordinate itself is positive. Substituting the strong identity gives `Qnat=I²`; at y=0 the auxiliary equation would force `Qnat*z²=1`, contradicting `Qnat>=4`. Likewise f=0 would make positive `Qnat` equal negative Delta.

The shifted graph inputs ensure `q>0`, `Y>0`, and `c>=2`, so the lower bound on Qnat needs no positive beta, J, X or gamma premise. The formal source takes all four ports as natural casts, a stronger local assumption than the mathematical sign analysis needs. The exact graph rows, residual vector order, magnitude and generic positivity source interfaces were checked; the author's receipt reproduces. The graph identities, arithmetic tactics, casts, dependencies and provider ancestry are still unelaborated, and no iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-fy-model-independent/check.py | cmp - reviews/ordinary13-residue90-fy-model-independent/result.json
python3 -I -S -B research/ordinary13-residue90-fy-model-draft/check.py | cmp - research/ordinary13-residue90-fy-model-draft/receipt.json
```
