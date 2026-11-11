# P73 thirteen-positive circuits: 91/30 and 90/50

This source-only packet gives two transformations of the P73 thirteen-positive 92-operation, degree-30 graph at the whole compact44 tuple:

| Graph | Live operations | Exact degree | Relationship to P73 |
| --- | ---: | ---: | --- |
| [p73_rewrite91_30.json](p73_rewrite91_30.json) | 91 | 30 | Entire polynomial is identical |
| [p73_90.json](p73_90.json) | 90 | 50 | Same zeros at each positive valuation |
| [p73_91.json](p73_91.json) | 91 | 50 | Intermediate before reassociation |
| [p61_92.json](p61_92.json) | 92 | 50 | Same-valuation zero transfer from the separate P61 93/34 graph |

The two primary graphs retain P73's same 13 positive inputs and four actual fixed integer ports, with no new fixed leaf. Integer leaves are free; additions, subtractions, multiplications, including numeral multiplication and squaring, each cost one operation. The exact-polynomial 91/30 graph strictly improves the inspected P73 92/30 record. The 90/50 graph strictly improves the inspected **same-port, same-domain** 90/55 and 90/51 records in degree at equal operation count; the 87/51 record uses fewer operations and has higher degree, so neither comparison dominates the other. These are comparisons with named records, not a global frontier or minimality claim.

P73's [ordinary proof](../../con-zfc-diophantine-forms/73-guard-reanchoring/positive/PROOF.md) inherits the native compiler and Pell-index interfaces and explicitly does not claim a new proof-assistant certificate. This packet proves the displayed finite algebraic relationships and checks the graphs and actual-byte degrees externally. It does not produce a new Lean theorem, bind a JSON file or rendered PDF inside Lean, independently rebuild the inherited compiler/calibration/foundational ancestry, or prove either side of the consistency statement.

## One exact-polynomial sharing

The P73 graph already computes `M=q3*qm`, with `q3=q³`, `qm=q−1`, `k=eta+zeta`, and computes `W=1+k*qm` only for `W*q3`. Replace the three operations

```
t = k*qm; W = 1+t; product = W*q3
```

by two operations

```
kM = k*M; product = q3+kM.
```

The identity `(1+k*qm)*q3=q3+k*(q3*qm)` holds over every commutative ring. The result replaces the value used by the first residual without altering any other node, so the entire output polynomial is equal for every assignment, not only at zeros. Applying it to the original graph gives 91/30; applying it to the intermediate 91/50 gives 90/50.

## Shared strong/auxiliary square

P73's four residuals include

```
As = f²−1 − Delta*(i*c²)²,
Aa = y² − Delta*(f²−1)*(y²−V²) − 1,
y = V+u,
Delta = (a+2)²−1,   a = X*Y+Y.
```

The graph already has `Delta*c²` for the main residual. Let

```
S = i*(Delta*c²),    As' = Delta*(f²−1) − S²,
Aa' = y² − S²*(y²−V²) − 1.
```

The following are exact polynomial identities:

```
As' = Delta*As,
Aa' = Aa + Delta*(y²−V²)*As = Aa + (y²−V²)*As'.
```

Every allowed positive input has `a>0`, hence `Delta>0`. Therefore `As'=0` iff `As=0`; on that common zero locus `Aa'=Aa`. The other two residuals stay exactly the same. A sum of four integer squares is zero iff each residual is zero, so replacing the pair `(As,Aa)` by `(As',Aa')` preserves the full zero set in **both directions at the same positive input tuple**. No auxiliary sign or extra witness condition is assumed.

The original five-node strong/auxiliary coefficient block is replaced by four nodes: `i*(Delta*c²)`, its square, `Delta*(f²−1)`, and the new strong subtraction. The common square also supplies the coefficient in `Aa'`. The gap is computed as `u*(y+V)`, exactly equal to `y²−V²` because `y=V+u`; this requires the same two gates as the old square-and-subtract gap. Thus the triangular transformation saves one gate without changing fixed leaves. P61 has the same relevant residual structure and applies identically, giving the separately recorded 92/50 scoped transfer.

## Reproduction and degree evidence

From the repository root run:

```
python3 -B Computability/DiophantineConsistency/research/ordinary13-p73-triangular91-50/check.py
```

The deterministic output is `result.json`. The checker pins the P73 and P61 graphs, P73 proof, P61 binding and P72's matching compact44 byte binding. It reconstructs every graph from its parent, checks topology and all gate, witness and port liveness, and verifies the sharing, triangular, difference-of-squares and first-norm identities in a small exact integer-polynomial ring. It verifies the compressed and little-endian raw hashes and lengths of all four P72 port payloads against the P61 binding; MF is the already-shifted port and is not shifted again.

For both degree-50 P73 graphs and the P61 transfer, direct syntactic degree propagation through the factored gap gives upper bound 50. For the identical-polynomial 91/30 graph, the syntactic bound 36 is improved to 30 using two exact cancellations: `y²−V²=u(y+V)` makes the auxiliary residual degree at most 13; and writing `root0=M*ell+d` with `deg d≤7` yields

```
A0 = d² + M*ell*(2*d−M*k) − M²,
```

of degree at most 15. The other two residuals have degree at most 14, so their squared sum has degree at most 30. The checker inspects the actual relevant source shapes and these finite bounds; it does not expand the giant full polynomial.

As independent lower bounds, the checker evaluates each **whole graph** on the ray where all 13 inputs are `t`, using the authenticated actual ports modulo 1,000,000,007. It obtains degree 50 with nonzero leading coefficient 832098066 for each triangular graph, and degree 30 with nonzero leading coefficient 103566611 for the exact-polynomial P73 rewrite. The modular ray and upper bounds give the stated exact specialized integer degrees. These are external degree checks, not Lean `totalDegree` theorems.
