# Current-port 71-operation degree-60 ordinary sphere candidate

The proposed equation has 14 strictly positive integer coordinates and the same four current2011 integer ports as the checked 67/94 graph. Let `P=N0`, `Q=N1`, `W=Nt`, `I=i*c²`, and

```
A = Delta*(f²−1)
U = A*(V²−y²)+y²
H = I²−A.
```

Its equation is `P²+U²+(Q*W−1)²+H²−2=0`. The graph reuses the first 61 rows of the 67/94 graph through `H`. It has 71 live binary operations (38 multiplications, 19 additions, 14 subtractions); all 14 coordinates and all four fixed ports remain live.

The all-model equivalence with 67/94 uses the existing IΣ₁-model facts that `P` and `U` are nonzero, so each square is at least one. A sphere zero forces both residual squares to zero and `P²=U²=1`. From `H=0`, the coefficient of `U` becomes `I²`, excluding `U=−1`; the existing negative-unit exclusions give `P=Q=U=W=1`. Conversely a 67/94 zero has its normalized strong factor `1+H=1` by its mod-four negative-unit exclusion; the other unit factors then force the sphere zero. A subsequent [Lean model join](../current2011-ordinary71-60-model-join/README.md) checks this same-valuation equivalence, and an independently reviewed [iPRA client](../current2011-ordinary71-60-ipra/README.md) checks both mapped refutation and Gödel–Gentzen consistency formulations. The graph-to-source and degree checks remain external, with the provider limits recorded in those packets.

`check.py` verifies the exact fixed-port bytes and complete graph/liveness. Its upper degree bound of 60 uses the pinned prior exact prefix certificate (including the main-norm cancellation); the factor bounds are `P:22`, `Q:18`, `U:30`, `W:2`, `H:22`. A full-graph evaluation over the actual-port residues on the ray all witnesses `t`, modulo 1,000,000,007, has degree 60 with nonzero leading coefficient 176,981,100. This proves exact specialized integer degree 60, with the stated inherited prefix certificate; it is not a Lean total-degree theorem. The maintained equation/PDF remains unchanged.

Reproduce from the repository root with `python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary71-60-candidate/check.py`. `build.py` refuses to overwrite the graph. No global minimum or fixed-port zero-existence conclusion is claimed.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `524b745087c117942789591b91a6020afee0819efe51b22709cd39a7e50450b8` |
| `polynomial.json` | `3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27` |
| `check.py` | `177975d7326466e7b02abcda8831d359a2a50552212d7835f062272705418ae5` |
| `result.json` | `06ff1bfcf9af75972b0e9e47796ade7bbdd9fc70f614705754526073888d6d7f` |

The original packet bytes are preserved under `history/initial/`; this revision corrects the coefficient directory path and makes the checker resolve that recorded path. The graph rows and port bytes are unchanged.
