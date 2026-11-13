# Current-port 71-operation degree-60 ordinary sphere candidate

The proposed equation has 14 strictly positive integer coordinates and the same four current2011 integer ports as the checked 67/94 graph. Let `P=N0`, `Q=N1`, `W=Nt`, `I=i*c²`, and

```
A = Delta*(f²−1)
U = A*(V²−y²)+y²
H = I²−A.
```

Its equation is `P²+U²+(Q*W−1)²+H²−2=0`. The graph reuses the first 61 rows of the 67/94 graph through `H`. It has 71 live binary operations (38 multiplications, 19 additions, 14 subtractions); all 14 coordinates and all four fixed ports remain live.

The intended all-model equivalence with 67/94 uses the existing IΣ₁-model facts that `P` and `U` are nonzero, so each square is at least one. A sphere zero forces both residual squares to zero and `P²=U²=1`. From `H=0`, the coefficient of `U` becomes `I²`, excluding `U=−1`; the existing negative-unit exclusions give `P=Q=U=W=1`. Conversely a 67/94 zero has its normalized strong factor `1+H=1` by its mod-four negative-unit exclusion; the other unit factors then force the sphere zero. This is a proof plan here; the separate Lean model attempt has not yet checked it. In particular no iPRA endpoint for this graph is claimed in this packet.

`check.py` verifies the exact fixed-port bytes and complete graph/liveness. Its upper degree bound of 60 uses the pinned prior exact prefix certificate (including the main-norm cancellation); the factor bounds are `P:22`, `Q:18`, `U:30`, `W:2`, `H:22`. A full-graph evaluation over the actual-port residues on the ray all witnesses `t`, modulo 1,000,000,007, has degree 60 with nonzero leading coefficient 176,981,100. This proves exact specialized integer degree 60, with the stated inherited prefix certificate; it is not a Lean total-degree theorem. The maintained equation/PDF remains unchanged.

Reproduce from the repository root with `python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary71-60-candidate/check.py`. `build.py` refuses to overwrite the graph. No global minimum or fixed-port zero-existence conclusion is claimed.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `3a1e34694930c9a73d81c73b995bee44f3118cbf11d46496c1fcdc36db4d3078` |
| `polynomial.json` | `d4d586406f56d1a179a8de199bf71fbcc86972d8817c8360322937a7bd60c358` |
| `check.py` | `295eff2be387f8689ac60e657b47a8ac30c74d614d0f07473c2cd04645012625` |
| `result.json` | `0664a39e95861c6c10498d028c2ed2e338eac2bac428a6ec261f6c68c9c5a72b` |
