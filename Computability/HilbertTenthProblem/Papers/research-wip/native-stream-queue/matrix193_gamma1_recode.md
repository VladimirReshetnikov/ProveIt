# A faithful 193-generator recoding with Pell parameter 391

The complete [saved array](matrix193_gamma1_recode.json) gives the same finite-input directed semigroup membership language as [S193](group_directed_semigroup193.md), with a faithful encoding of all twenty active upper letters. Its universal block `W=01010111` has trace **−28**, so the even block has Pell parameter **391**, instead of 1057 in the [previous Schreier recoding](matrix193_schreier_recode.md).

A further property of the new upper group makes its **first row injective**. Consequently the variable target needs only two upper coordinates; from correctly indexed Pell coordinates their generic assembly costs **6=4M+2A**, rather than the four-entry 12-operation assembly. The lower target is unchanged and fixed. This is an exact projected membership interface, not a completed Diophantine representation: neither the exact Pell index nor the unbounded membership certificate has been paid. The complete universal arithmetic bound remains 84.

The largest generator coefficient also falls relative to the previous 1057 recoding, but total coefficient bits increase. No trace, coefficient or loader optimality is asserted.

## 1. A small modular free group, with an explicit graph proof

Put

```
T = [[1,1],[0,1]],       U = [[1,0],[5,1]],
V0 = [[-14,-9],[25,16]], V = [[-9,5],[-20,11]].
```

The matrices T, U, V0 freely generate Gamma_1(5), where here

```
Gamma_1(5) = { [[a,b],[c,d]] in SL2(Z): a=d=1 mod5, c=0 mod5 }.
```

The following graph verifies the precise basis; it does not infer freeness from small relation tests. Use the standard modular presentation

```
PSL2(Z) = <s,r | s²=r³=1>,
s represented by [[0,-1],[1,0]], r by [[0,-1],[1,1]].
```

For this presentation see [Milne, Modular Functions and Modular Forms, Remark 2.14](https://www.jmilne.org/math/CourseNotes/MF110.pdf), printed page 28. The finite graph below is the quotient of the free-product tree; its trivial vertex stabilizers make it an ordinary graph. The maximal-tree basis theorem is [Hatcher, Proposition 1A.2](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf), printed page 84. These are the inherited group/graph facts; the entire finite instance is given and checked here.

Let the twelve edges be the nonzero row vectors of F5² modulo sign, represented in the following order. The columns s and r give right multiplication followed by sign normalization. The last column gives the two endpoint orbit numbers: six s-orbits numbered 0 through 5 and four r-orbits numbered 6 through 9.

| Edge | Vector | s | r | Endpoints |
|---:|---|---:|---:|---|
| 0 | (0,1) | 2 | 3 | (0,6) |
| 1 | (0,2) | 7 | 9 | (1,7) |
| 2 | (1,0) | 0 | 0 | (0,6) |
| 3 | (1,1) | 6 | 2 | (2,6) |
| 4 | (1,2) | 11 | 8 | (3,8) |
| 5 | (1,3) | 8 | 10 | (4,9) |
| 6 | (1,4) | 3 | 4 | (2,8) |
| 7 | (2,0) | 1 | 1 | (1,7) |
| 8 | (2,1) | 5 | 6 | (4,8) |
| 9 | (2,2) | 10 | 7 | (5,7) |
| 10 | (2,3) | 9 | 11 | (5,9) |
| 11 | (2,4) | 4 | 5 | (3,9) |

Neither permutation has fixed points; their orbit sizes are exactly two and three. The action is transitive. The stabilizer of edge 0 is the projective image of Gamma_1(5). Thus its quotient graph has twelve edges and ten vertices, with free rank three. Equivalently, the s² and r³ pieces of the Schreier complex contract to the displayed orbit vertices without leaving torsion stabilizers.

Take the nine tree edges `0,1,3,4,5,6,8,9,10`, based at orbit vertex 6. The non-tree edges 2, 11 and 7 give the following matrix representatives (the helper also saves their exact s/r words):

```
edge2:  [[-1,1],[0,-1]] = -T^-1,
edge11: [[-4,-1],[5,1]] = T^-1 U,
edge7:  [[14,9],[-25,-16]] = -V0.
```

The cusp loops T and U have chord words `edge2^-1` and `edge2^-1 edge11`. Hence changing from these three chord generators to T, U, V0 is an invertible free-basis change. Central signs disappear projectively. Each of T, U, V0 is in Gamma_1(5), which excludes −I; the projective isomorphism therefore lifts faithfully to the stated integral matrices.

Finally replace the third basis element by

```
V = T V0 T^-1 U T^-1.
V0 = T^-1 V T U^-1 T.
```

This is an explicit invertible Nielsen change fixing T and U. It proves that T, U, V are a free basis, as needed below.

## 2. Twenty letters and a missing lower-parabolic loop

Over the rose with labels T, U, V, take a connected **immersed** graph with vertices 0 through 9 and positive labeled edges as follows:

* T fixes 0 and cycles `1→2→...→9→1`.
* U has a self-loop at every vertex except 1; at 1 there is no U edge in either direction.
* V interchanges 0 and 1 and fixes 2 through 9.

Each label has at most one incoming and outgoing edge per vertex, so this is an immersion. It is not a complete finite cover. A reduced nonempty graph loop maps to a reduced nonempty free-group word, proving injection. There are 29 edges, 10 vertices and rank 20.

Use the V edge `0→1` followed by the eight T edges `1→...→9` as a spanning tree. With base 0, its twenty free generators are

```
T, U,
V², V T^9 V^-1,
V T^r U T^-r V^-1       (r=1,...,8),
V T^r V T^-r V^-1       (r=1,...,8).
```

Call this subgroup H. Move the basepoint to vertex 1, equivalently replace H by H'=V^-1 H V. Its basis becomes

```
V^-1 T V, V^-1 U V,
V², T^9,
T^r U T^-r             (r=1,...,8),
T^r V T^-r             (r=1,...,8).
```

Assign the tape letters

```
a = Psi(0) = V^-1 T U V,
b = Psi(1) = V^-1 U^-1 V.
```

This is another invertible basis change: the first two displayed generators are `ab` and `b^-1`. Assign the remaining eighteen basis matrices to `A,...,O,[,],#`. To specify the literal coefficient ledger, number these extras in order as V², T^9, the eight U-conjugates, then the eight V-conjugates; use the zero-based permutation

```
[0,10,4,3,15,13,6,14,9,1,16,11,12,5,8,7,2,17].
```

This is a selected permutation found by a bounded coefficient probe, not an exhaustive optimization claim. The archived legacy letter X remains unused. The result is a faithful map of the complete twenty-letter free group.

At the new basepoint 1 no nonzero power of U can be read, because its first edge in either direction is absent. The immersed-core theorem, or reduced-word path lifting directly, gives

```
H' intersect <U> = {I}.
```

All these matrices remain in Gamma_1(5). A lower unipotent `[[1,0],[k,1]]` belongs to Gamma_1(5) exactly when 5 divides k; then it is U^(k/5). Therefore H' contains no nonidentity lower unipotent at all. This is a statement for every group element, not only for a bounded sample of positive products.

## 3. Literal directed semigroup transfer and the projected target

Keep every parent rule, tile and identifier, terminal `[J1]`, lower code and directed-generator convention. The lower code uses

```
P=[[1,2],[0,1]], Q=[[1,0],[2,1]],
x_i=Q^-i P Q^i, t=P.
```

For all 96 retained tiles `(g_i,h_i)`, emit

```
A_i = diag(Psi(h_i), x_i),
B_i = diag(Psi(g_i)^-1, t^-1 x_i^-1 t),
C   = diag(Psi([J1]#)^-1, t).
```

The target for finite configuration w is `diag(Psi(w#)^-1,t)`. The full source thus has exactly 193 generators. Every lower block is unchanged, so the parent's positive-product shape theorem applies. Faithfulness of the new upper alphabet then yields exactly the same word equation and finite-input language. This preserves the original conditional universality/Neary–Woods dependency and the full twenty-letter context/state encoding; it is not a tape-pair-only recoding.

There is also an exact reduction of target coordinates. If M,N in H' have the same first row, the matrix NM^-1 has first row (1,0). Its determinant is one, so it is a lower unipotent. The preceding intersection result forces NM^-1=I, hence M=N. All actual upper product blocks and all encoded targets belong to H'. Thus matching the two upper first-row entries is equivalent to matching the whole upper target on this membership problem.

For the lower block, matching entries (11,12,21) to (1,2,0) forces entry 22 to equal 1 by determinant one. Every generator and product is already block diagonal with determinant-one blocks. Consequently the five-entry predicate consisting of **two varying upper entries and three fixed lower entries** is exactly the original matrix-target membership predicate. No determinant, integrality or subgroup-membership oracle is added: these hypotheses follow from the actual generated products. The result is not a projection equivalence for arbitrary unrelated integer matrices.

## 4. The smaller universal block and its six-operation interface

Before conjugation, `(ab)^3 b²` is `T³U^-2=[[-29,3],[-10,1]]`. In the actual code,

```
Psi(W) = [[1861,-1037],[3390,-1889]],       trace=-28,
B=Psi(W²)=[[-52109,29036],[-94920,52891]],
a0=391, Delta0=152880,
D=B-a0 I=[[-52500,29036],[-94920,52500]],
D²=152880 I.
```

For every natural x,

```
B^x = chi_391(x) I + psi_391(x) D,
B^-x = chi_391(x) I - psi_391(x) D.
```

The existing [unary block initialization](u15_unary_block_interface.md) on padded length 2x+4 supplies the universal finite word `U_S (W²)^x V_S`; the contexts are fixed after selecting the program. With `L=Psi(V_S#)^-1` and `R=Psi(U_S)^-1`, its upper target is

```
chi_391(x) (LR) - psi_391(x) (LDR).
```

Only entries 11 and 12 are needed. Set A=LR and C=−LDR as fixed coefficient matrices. The complete generic varying-coordinate assembly is

```
a=A11*chi; b=C11*psi; target11=a+b;
c=A12*chi; d=C12*psi; target12=c+d.
```

It costs four multiplications and two additions. Constant degeneracies may reduce specialized instances; no such reduction is assumed in this ledger. This count is conditional on correctly indexed supplied chi,psi. The Pell norm alone does not enforce index x, and the fixed positive-semigroup membership predicate still needs its own unbounded arithmetic certificate. Neither cost is hidden in the six gates. No affine unary loader or complete six-gate universal polynomial is claimed.

## 5. Full resource and replay evidence

| Resource | Original S193 | Previous Pell1057 recoding | This recoding |
|---|---:|---:|---:|
| Generators | 193 | 193 | 193 |
| Matrix entry slots | 3,088 | 3,088 | 3,088 |
| Nonzero entries | 1,543 | 1,541 | 1,543 |
| Maximum absolute entry | 1,304,111,120 | 5,094,184,660 | 538,008,330 |
| Maximum magnitude bits | 31 | 33 | 30 |
| Total magnitude bits | 19,321 | 20,785 | 23,832 |
| Even-block Pell parameter | 39,979,681 | 1,057 | 391 |
| Generic conditional target assembly | 12 | 12 | 6 |

Magnitude bits mean `bit_length(abs(entry))`, with zero contributing zero. These are complete literal array statistics, not compressed-description or arithmetic-operation costs. The first-row projection is a new theorem for this group; the old columns record the established four-entry assembly and do not claim that twelve is optimal for those codes.

The [fresh checker](matrix193_gamma1_recode.py) authenticates five predecessor data/proof files, reconstructs all 3,088 original entries, checks both finite graphs and the exact basis words/Nielsen matrices, and emits every new entry. It verifies all 193 retained lower blocks, 386 block determinants, and pairwise distinctness of the 193 new matrices. It never imports or executes predecessor Python.

The inherited accepted input `[110A0]` uses the same 167 generator factors. Their fully materialized new product equals

```
[[-68793567899, 427044708833, 0, 0],
 [ -8045721300,  49944825001, 0, 0],
 [           0,            0, 1, 2],
 [           0,            0, 0, 1]].
```

Thirteen positive/negative power pairs check the Pell formula, and thirteen fixed-context checks verify the projected target arithmetic. The graph and quadratic-algebra arguments prove the unbounded claims; finite examples are not substituted for them.

The bounded CLI reads pinned data, rejects duplicate/nonfinite JSON, and compares exact JSON types through canonical serialization. Checks use explicit exceptions and remain active under optimized Python. From any directory:

```sh
python3 /absolute/path/matrix193_gamma1_recode.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_gamma1_recode.json
```

Use the mutually exclusive `--output FILE` to write the receipt. Fresh normal and `-O` exact replays from `/` pass. All predecessor packets remain unchanged. This packet asserts a faithful complete matrix recoding and a conditional target-interface saving, with the ordinary-input index and history obligations explicitly unpaid; it asserts no new complete Diophantine operation bound.
