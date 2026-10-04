# Literal unit-shear controllers for the actual matrix193 tables

The actual saved context-absorbed 96 paired matrices and LOAD matrix have a tractable signed-unit-shear expansion: **32,819 shear edges**, plus SWITCH and IDLE, giving **32,821 edges** and padded lane count **65,536**. The original fixed Gamma1 table is smaller: **19,611 shear edges**, giving **19,613 edges** and padded lane count **32,768** when its single matrix SWITCH and IDLE are included.

The [helper](matrix193_unit_shear_controller.py) and [receipt](matrix193_unit_shear_controller.json) save every exact run-length word, every expanded physical word, and both complete controller edge tables. They reconstruct both tables from pinned inert data and verify all **386 matrix factorizations** and **52,430 unit steps** exactly. No predecessor Python is executed or imported. This is a controller compilation packet, not a newly emitted complete history-polynomial DAG.

## 1. Exact input tables and scope

The ten authenticated source/proof/receipt dependencies are listed with exact SHA256 pins in the receipt. The current context table is reconstructed from [context absorption](matrix193_context_absorption.md), then compared entry for entry with all 96 records in [synchronized rows](matrix193_synchronized_rows.md). The original table is reconstructed separately from the complete [Gamma1(5) array](matrix193_gamma1_recode.md).

For each array, write its upper generator blocks as

```
A_i: H_i,   B_i: G_i^-1,   central generator: C.
```

The emitted paired transitions are `K_i=C^-1 H_i C` and `G_i`, in the literal retained tile-ID order. The additional LOAD matrix acts only on the second row and is

```
B0^-1 = [[52891,-29036],[94920,-52109]].
```

All inverses and products here are computations on fixed integer data. Determinant one is checked before every inversion. No variable matrix inverse enters a history source.

The context-absorbed array uses the saved contexts `[110` and `A0]`. That fixture is **not asserted to be a universal compiled program**. Its controller size is a concrete property of those fixed matrices; program-dependent context absorption can change matrix coefficients, shear lengths and lane count. The 32,821-edge result therefore does not give a uniform universal operation count.

For the original table, the fixed central upper matrix is

```
C0 = [[-31653619,195915076],[-3702035,22913161]].
```

Its 96 pairs and LOAD do not depend on contexts. Section 4 states the separate matrix-SWITCH interface that retains this fixed table, without hiding the arithmetic needed to compile that switch into a packed certificate.

## 2. Balanced Euclidean factorization

Use

```
U(q)=[[1,q],[0,1]],   L(q)=[[1,0],[q,1]].
```

For `M=[[a,b],[c,d]]` of determinant one, repeatedly reduce whichever of `|a|,|c|` is larger. If `|a|>=|c|>0`, choose the nearest integer `q` to `a/c` and left-multiply by `U(-q)`. Otherwise choose the nearest integer to `c/a` and left-multiply by `L(-q)`. Exact ties are rounded toward positive infinity. The checker proves at every step that the remainder has absolute value at most half the divisor, the sum `|a|+|c|` strictly decreases, and determinant one is preserved. Thus the algorithm terminates; it is not a bounded search for a factorization.

If left reductions are `R1,...,Rk` in chronological order, then

```
Rk ... R1 M = Mfinal,
M = R1^-1 ... Rk^-1 Mfinal.                        (1)
```

Accordingly the source records inverse reduction factors in chronological order, not reverse order. If the surviving first-column pivot is in the second row, one final left multiplication by

```
J=[[0,-1],[1,0]],  J^-1=U(1)L(-1)U(1)
```

moves it to the first row. The resulting upper triangular matrix has diagonal entries both `1` or both `-1`. In the former case it is `U(b)`; in the latter it is `(-I)U(-b)`, where

```
-I=(U(1)L(-1)U(1))².
```

These explicit fixed words complete the factorization. Adjacent equal-axis runs are merged by adding their integer exponents, and zero runs are removed. This is exact simplification; no shortest-word or globally optimal quotient claim is made.

Each run is then expanded literally into `|q|` signed unit shears. For right actions on row coordinates:

| Label | Update |
|---|---|
|1,2|`X0 += X1`, `X0 -= X1`|
|3,4|`X1 += X0`, `X1 -= X0`|
|5,6|`Y0 += Y1`, `Y0 -= Y1`|
|7,8|`Y1 += Y0`, `Y1 -= Y0`|

Thus `U(q)` changes a row's second coordinate, and `L(q)` changes its first. A paired TILE word executes the K word on X followed by the G word on Y. The two row actions are disjoint. The helper independently multiplies each run-length word and each expanded unit word and obtains the original matrix or pair exactly.

## 3. Complete private-path controllers and costs

Macro 0 is LOAD, based at hub 0. Macros 1 through 96 are TILEs, based at hub 1 in the inherited tile order. Give every macro a private path with one edge per literal unit shear. Internal states are all distinct, with exactly one incoming and one outgoing edge. Then add one SWITCH edge `0 -> 1` and one IDLE edge `1 -> 1`. Edge 0, the first edge of the LOAD macro, is the unique marked population edge.

The controller recognizes completed LOAD cycles, one SWITCH, then completed TILE cycles and IDLEs. Internal states cannot create a partial accepted macro or a transition between private paths. The LOAD mark counts cycles, not all uses of its physical shear label by TILEs.

| Resource | Saved context-absorbed table | Original fixed table |
|---|---:|---:|
| Matrix factorizations |193|193|
| Run-length factors |7,176|4,780|
| Expanded unit shears |32,819|19,611|
| LOAD word length |40|40|
| Largest run magnitude |11|10|
| Longest individual matrix word |238|186|
| Longest paired TILE word |370|236|
| Maximum fixed matrix-entry bits |103|84|
| Controller edges, including SWITCH/IDLE |32,821|19,613|
| Controller states |32,724|19,516|
| Largest state code |32,723|19,515|
| Padded power-of-two lanes m |65,536|32,768|

The complete receipt schema is stable:

* `packets[0]` is `saved_context_absorbed`; `packets[1]` is `original_fixed_table`.
* `controller.edges` contains rows `[edge_id,source,target,physical_label_or_R,macro_id_or_null]`.
* Each macro record saves its name, tile ID, hub, first/last edge, full physical word, matrices, exact RLE factors and Euclidean quotient sequence.
* In the original table, edge 19611 is `[19611,0,1,"R",null]`; edge 19612 is its identity IDLE. The R tag is intentionally not a signed unit shear.
* In the contextual table, edge 32819 is the identity SWITCH, and edge 32820 is IDLE.

For the contextual table, the complete construction bound proved in [marked-loader packing](matrix193_marked_loader_packing.md) now has actual numerical controller data:

```
9n+3log2(m)+210 = 295647 operations,
n+29 = 32850 positive integer witnesses.
```

For example `Hfix=35426322` covers both its fixed initial row and its padded lane margin. This is an instantiated **construction upper bound** for an effective fixed-arity polynomial recognizing that saved-context language. It is not the ledger of a 295,647-row array emitted by this packet. The full controller and all its coefficients are present; the arbitrary-duration history source follows the explicit inherited recipe. Its witness count is independent of duration.

For comparison only, substituting the original table's `n,m` into the old **identity-switch** formula gives 176772 operations and 19642 witnesses. That number is **not** claimed for the arbitrary-context R-switch interface below: its additional selected-source/range arithmetic must be emitted and counted. This packet does not assign a free cost to a fixed 2x2 matrix acting on variable packed histories.

## 4. Fixed original table with a context matrix switch

This section identifies why the smaller original table is useful; its packed arithmetic is a separate obligation. Let the fixed contexts give the inherited constants

```
L=Psi(V#)^-1, R=Psi(U)^-1.
```

Start `X=e1*L^-1*C0`, `Y=e1`. Perform exactly x fixed LOAD macros, then one SWITCH `Y -> Y*R`, then an arbitrary common word of the original fixed TILE pairs. The terminal rows are

```
X=e1*L^-1*H(word)*C0,
Y=e1*B0^(-x)*R*G(word).                            (2)
```

Both underlying matrices lie in the inherited first-row-injective group. Hence equality of these rows is equivalent to

```
H(word)*C0*G(word)^-1 = L*B0^(-x)*R,               (3)
```

the original fixed193 membership target for the ordinary input word `U (W²)^x V`. This is the correct multiplication order. It moves context dependence into fixed initial constants and one matrix switch, while retaining fixed unit TILE/LOAD words. It does not require program-dependent expansion of R into extra unit edges.

The actual context-conjugation identities are checked for every retained tile:

```
Ccontext=L^-1*C0*R^-1,
Kcontext_i=R*Koriginal_i*R^-1,
Gcontext_i=R*Goriginal_i*R^-1.                      (4)
```

The LOAD-count proof can still read the typed pre-state of the switch, where `Y=e1 B0^-k`, before multiplication by R. However, the native packing proof must be extended to enforce this new selected fixed-matrix action, including carry/range bounds and all constant multiplications. The existing identity-switch polynomial cannot silently be reused. No such full DAG or universal count is asserted here.

## 5. Genuine finite trajectories and reproduction

The saved accepting tile word has 83 TILEs at ordinary input `x=0`. The helper checks the entire contextual expanded trajectory: 24,350 unit steps and one identity switch, reaching equal rows. It also checks the original-table version with the actual saved R switch: 12,894 unit steps and one matrix switch, reaching equal rows. The largest intermediate coordinate sizes are 484 and 475 bits respectively. Every private controller transition and every physical row update is evaluated exactly. The two final states satisfy the expected right-R frame identity.

These are actual finite-input witnesses inherited from the saved accepted configuration `[110A0]`; they are not evidence of universality for its contexts or a materialized positive native Pell tuple. The packet independently verifies all table entries, not only the tiles visited by this witness. Exact Euclidean descent and the group/controller arguments establish the unrestricted statements.

The receipt also pins the fresh helper bytes, rejects duplicate or nonfinite JSON, and uses recursive type-exact comparisons. From any working directory:

```
python3 matrix193_unit_shear_controller.py --root /absolute/path/native-stream-queue --expect /absolute/path/matrix193_unit_shear_controller.json
python3 -O matrix193_unit_shear_controller.py --root /absolute/path/native-stream-queue --expect /absolute/path/matrix193_unit_shear_controller.json
```

Use the mutually exclusive `--output` to write a receipt. The source and receipt are complete for matrix factoring and finite controller generation; historical source scripts are neither loaded nor invoked. Fresh normal and optimized exact receipt replays from `/` both passed.
