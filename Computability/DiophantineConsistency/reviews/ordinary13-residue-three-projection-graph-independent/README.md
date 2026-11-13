# Independent source review: actual-graph q divides 3X

The proposed `actual_main_balance` uses the actual signed-pair norm and calls direct main orientation with `R'=R+X*Y*q`. Its returned positive root satisfies `P=N+U*main`; the source's negative linear combination correctly restates this as `U*main+H*k=P`, with the essential `X*Y*q` term retained. U>0, Y>=8, k>0 and F<=q are explicit at that interface.

The graph client derives those scale assumptions from its stated positive J/beta and shifted natural coordinates, and obtains the truncated-rank bound from its explicit positive-C gap. It takes the conditional exact-index output `2n=R+1` and `k=2n+4Q*w`, giving the exact decomposition required by the separately reviewed fact-level `q_dvd_threeX` certificate. Its theorem concludes only `q | 3X`; it does not assume or establish Bézout, `q | X`, a power representation or eta-zero generalization.

The 90 graph zero, natural port representation, positive J/beta/X, positive-C gap and rank window remain explicit. All inherited graph norm, shifted-eta auxiliary/exact-index, provider and compact-byte/PDF boundaries remain unelaborated or separate. The author receipt reproduces; finite source controls are not a Lean proof or an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-three-projection-graph-independent/check.py | cmp - reviews/ordinary13-residue-three-projection-graph-independent/result.json
python3 -I -S -B research/ordinary13-residue-three-projection-graph-draft/check.py | cmp - research/ordinary13-residue-three-projection-graph-draft/receipt.json
```
