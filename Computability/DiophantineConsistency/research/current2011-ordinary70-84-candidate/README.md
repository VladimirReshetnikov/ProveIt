# Current-port 70-operation degree-84 ordinary sphere candidate

The equation uses 14 strictly positive integer coordinates and the four current2011 integer ports. Let `P=N0`, `Q=N1`, `W=Nt`, `I=i*c²`,

```
A = Delta*(f²−1)
U = A*(V²−y²)+y²
H = I²−A.
```

Its equation is `U²+(P*Q*W−1)²+H²−1=0`. The graph reuses the first 61 rows of the 67/94 graph through `H`. It has 70 live binary operations (38 multiplications, 18 additions, 14 subtractions); all 14 coordinates and four integer ports remain live. It is a tradeoff between 67/94 and 71/60; it does not replace the maintained equation/PDF.

The all-model equivalence to 67/94 uses the existing model fact `U ≠ 0`, giving `U² ≥ 1`. A sphere zero forces `U²=1`, `P*Q*W=1` and `H=0`. The last identity rewrites the coefficient of `U` to the square `I²`, excluding `U=−1`; the known exclusions `P≠−1` and `Q≠−1` then force `U=P=Q=W=1`. Conversely the five unit factors of a 67/94 zero satisfy the sphere equation. A later [Lean model join](../current2011-ordinary70-84-model-join/README.md) checks this same-valuation equivalence, and an independently reviewed [iPRA endpoint](../current2011-ordinary70-84-ipra/README.md) checks the mapped refutation and Gödel–Gentzen consistency formulations. The graph-to-source and degree checks remain external, with provider limitations stated in those packets.

`check.py` authenticates the exact current port bytes and the entire graph/liveness. Using the pinned previous exact prefix certificate for its upper bound, the relevant factor degrees are `P:22`, `Q:18`, `U:30`, `W:2`, `H:22`, yielding degree at most 84. Evaluation of the complete graph on the ray all witnesses `t`, over the actual-port residues modulo 1,000,000,007, gives degree 84 and nonzero leading coefficient 589,155,221. Thus the specialized integer polynomial has exact degree 84, conditional on the audited prefix certificate. This is an external finite degree check, not a Lean total-degree theorem.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary70-84-candidate/check.py
```

`build.py` refuses to overwrite the graph. No global minimum or fixed-port zero-existence conclusion is claimed.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `3f247eddc24d729ee53e41f37bf93d037e11c5a5b0ee15b01b589dd74d144cf7` |
| `polynomial.json` | `bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5` |
| `check.py` | `28d871b8d44e8eac7d65c223234c3d0318c2a04afdeebdfe08974eb191b77620` |
| `result.json` | `45c539841de3f3b22fa7be8e35fd50e9abd2ce97864210d3e2ff296bcd9b0fc3` |
