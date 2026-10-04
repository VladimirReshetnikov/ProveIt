# A faithful 193-generator recoding with Pell parameter 1057

The complete [recoded array](matrix193_schreier_recode.json) preserves the
finite-input membership language of the fixed directed 193-generator
semigroup, while changing its faithful upper alphabet embedding. The
universal repeated input block `W=01010111` now has matrix trace **−46**, and
its square has Pell parameter **1057**, down from **39,979,681**. All twenty
active upper letters, including the separator and state symbols, remain
freely encoded. This is a complete matrix construction, not merely a
representation of the two tape letters.

This improves the fixed coefficient in an indexed-power interface. It does
not reduce the arithmetic operation count: the conditional target assembly
still costs 12 operations, and its exact index relation and the unbounded
membership certificate remain unpaid. The complete universal Diophantine
bound remains 84. The largest matrix entry increases, so the smaller Pell
parameter is a tradeoff rather than a reduction of every coefficient metric.

## 1. A checked twenty-element free basis

Use the parent's free matrices

```
P=[[1,2],[0,1]], Q=[[1,0],[2,1]].
```

Their freeness is the same inherited ping-pong premise as in
[S193](group_directed_semigroup193.md). To encode twenty letters while
controlling the first two, take the following explicit 19-sheet covering
of the graph with two loops labeled P and Q. Its vertices are 0 through18.
The positive P edges fix0 and cycle `1→2→...→18→1`. The positive Q edges
interchange0,1 and fix every other vertex. Both label actions are
permutations, so each vertex has exactly one incoming and outgoing edge
of each label. The graph is connected.

Take as a spanning tree the Q edge from0 to1 and the seventeen P edges
from1 through18. The tree path to vertex v>=1 is `Q P^(v-1)`; the path
to0 is empty. Each of the twenty remaining oriented edges gives a loop
by adjoining its two tree paths. The resulting free basis is exactly

```
P, Q^2, Q P^18 Q^-1,
Q P^r Q P^-r Q^-1,       r=1,...,17.
```

The graph has38 edges,19 vertices and18 tree edges, giving free rank20.
For the general covering and spanning-tree facts, see the primary graph
treatment [Stallings, Topology of Finite Graphs](https://doi.org/10.1007/BF02095993);
the precise maximal-tree basis and covering injection are also stated in
[Hatcher, Proposition1A.2 and Theorem1A.4](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf),
printed pages84–85. Here every edge, tree path and non-tree loop is checked
explicitly; freeness follows from that graph theorem, not a bounded search
for nontrivial relations.

Replace the first two free generators by

```
a=P Q^2, b=Q^-2.
```

This is an invertible change of free basis: `P=ab`, `Q^2=b^-1`.
Assign a to tape letter0 and b to tape letter1. Assign the remaining
eighteen displayed basis words, in order, to
`A,B,...,O,[,],#`. The inactive legacy symbol X is not part of this
twenty-letter alphabet. This yields a faithful map Psi from the entire
active alphabet free group into SL2(Z).

The construction of the covering and the smaller tape-pair image was
independently derived during review. The literal recoding below uses this
finite cover, rather than an unverified extension of a two-letter map.

## 2. All193 generators and the unchanged membership theorem

Keep all91 rewrite rules, all96 directed tiles, every tile identifier,
the terminal `[J1]`, and the parent lower embedding. In particular the
lower marker is `t=P` and the lower tile letter is `x_i=Q^-i P Q^i`.
For every retained tile emit the full integer matrices

```
A_i=diag(Psi(h_i),x_i),
B_i=diag(Psi(g_i)^-1,t^-1 x_i^-1 t),
C=diag(Psi([J1]#)^-1,t).
```

The target for a finite configuration word w becomes
`T_new(w)=diag(Psi(w#)^-1,t)`. All inverses are of the entire determinant-one
word matrix. No inverse generator is added to the directed semigroup.

Every lower block is identical to the parent's. Hence its lower-marker
argument still forces every positive product at a target to have the form
`A_(i1)...A_(id) C B_(id)...B_(i1)`. Faithfulness of Psi turns its upper
equality into precisely the same literal word equation

```
w# h(s) = g(s) [J1]#.
```

The existing directed correspondence and U15 simulation theorem therefore
apply unchanged. Equivalently, identify both faithful upper images with
the same abstract alphabet free group and leave the lower group fixed.
This gives an isomorphism between the two generated matrix semigroups and
preserves every generator-word equality to the corresponding target.
Thus finite-input membership has exactly the same language, not only the
same saved accepting example. Its inherited many-one r.e.-completeness
and the [universal repeated-block initialization](u15_unary_block_interface.md)
survive. No new arbitrary-program compiler is claimed to have been run.

## 3. The new indexed-power interface

The chosen letters satisfy `Psi(01)=P`, so

```
Psi(W)=Psi((01)^3 11)=P^3 Q^-4
      =[[-47,6],[-8,1]],
det=1, trace=-46.
```

For the even block B=Psi(W^2), direct multiplication gives

```
B=[[2161,-276],[368,-47]],
a0=trace(B)/2=1057,
D=B-a0 I=[[1104,-276],[368,-1104]],
Delta0=a0^2-1=1117248,
D^2=Delta0 I.
```

Therefore at every natural x the exact identities are

```
B^x=chi_1057(x) I+psi_1057(x) D,
B^-x=chi_1057(x) I-psi_1057(x) D.
```

Use the already proved source initialization on unary lengths2x+4, so
the ordinary input occurs as `(W^2)^x` between fixed contexts. With
`L=Psi(V_S#)^-1`, `R=Psi(U_S)^-1`, the upper target is
`chi_1057(x)*(LR)-psi_1057(x)*(LDR)`. Two multiplications and one addition
per entry give the same generic **12=8M+4A** assembly from correctly
indexed coordinates. Both fixed context matrices remain computable from
the selected program; their coefficients are not additional varying inputs.

The Pell norm alone still fails to impose the index x, and exponential
growth still prevents an arithmetic straight-line loader using x alone.
The smaller parameter removes neither of these obligations. This report
claims neither a minimal possible trace nor an arithmetic saving inferred
from coefficient magnitude.

## 4. Complete resources and bounded evidence

| Resource | Original S193 | Recoded S193 |
| --- | ---: | ---: |
| Generators |193|193|
| Matrix entry slots |3088|3088|
| Nonzero slots |1543|1541|
| Maximum absolute entry |1304111120|5094184660|
| Maximum magnitude bits |31|33|
| Sum of entry magnitude bits |19321|20785|
| Even-input-block Pell parameter |39979681|1057|

Magnitude bits are `bit_length(abs(entry))`, with zero contributing zero;
they omit sign bits and are not a compressed-description cost. The upper
recoding increases some coefficients despite lowering the block parameter.
All193 matrices are pairwise distinct and have determinant one. Every
lower block, rule, tile, source configuration and terminal word is retained.

The [fresh helper](matrix193_schreier_recode.py) reads four pinned files as
data and executes no predecessor or archived Python. It reconstructs all
3088 parent entries first, checks the complete cover and its twenty basis
loops, then emits all3088 new entries. It checks every retained lower block,
the two block determinants of every new generator, and matrix distinctness.

The saved accepted input `[110A0]` uses the same83 tiles and167 generators.
The helper verifies its full word equation and every entry of its recoded
4-by-4 product against the recoded target. This is a complete materialized
finite accepting product, distinct from the unbounded universal compiler
theorem. Thirteen exact positive and negative powers also check the new
Pell formula; the quadratic-algebra identity proves it for every x.

From any working directory, using only Python's standard library:

```sh
python3 /absolute/path/matrix193_schreier_recode.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_schreier_recode.json
```

The mutually exclusive `--output FILE` writes a receipt. JSON parsing
rejects duplicate keys and nonfinite constants; exact comparison preserves
JSON types. Checks use explicit exceptions. Fresh normal and optimized
replays from `/` pass. The pinned predecessor packets remain unchanged.
