# Independent chronological packing review

Date: 2026-10-04. Result: the final slice-only construction is sound and complete over positive integer input and positive integer witness leaves, conditional on the explicitly approved POWER and Sub semantic theorems. No additional history oracle, digitwise variable product, AND, or SPREAD is required. The proposed coefficient bound is sufficient. This review is of the construction and its mathematical semantics, not of a subsequently emitted arithmetic DAG or its operation/degree ledger.

## Sources and convention

Read as inert data only:

- `../sources/matrix193_countdown_rows.md`
- `../sources/matrix193_synchronized_rows.md`
- `../sources/matrix193_countdown_rows.json`
- `/workspace/shared/sandpile-repeated-target-20261004/SOURCE_NOTES.md`

No predecessor program, checker, stored trajectory, or repository code was executed. A newly written short Python calculation read the JSON's fixed matrix lists to check the numerical radix constants below. Its JSON SHA256 was `f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0`.

Let `z=(X0,X1,Y0,Y1)` be a column of coordinates. The original row-vector right action means that the fixed four-by-four tile matrix is `A_i=diag(K_i^T,G_i^T)`, with transposes. For LOAD, the four rows of `A_0` are

```
(1,0,0,0)
(0,1,0,0)
(0,0,52891,94920)
(0,0,-29036,-52109).
```

Write `a=(35426321,-19628667,1,0)` for the signed initial row coordinates, and `c_ir=1-sum_s A_i[r,s]` for the fixed offset correction. These two uses must not be confused in an implementation.

## Exact system reviewed

The external input `x` is a positive integer. Choose positive duration `h`, natural `ell`, `H=2^ell`, `D=2H`, and a fixed power of two `C>=128` such that

`C >= 2 + max_(i,r)(sum_s |A_i[r,s]| + |c_ir|)`.

Set `b=CD`, obtain `W=b^h`, and require natural `R` to satisfy `(b-1)R+1=W`. Require `H>max_r|a_r|`, `x<D`, and four natural endpoint offsets `f_r<D`, with `f_0=f_2` and `f_1=f_3`.

For `i=0,...,96`, take natural selectors `E_i`, with `Sub(R,E_i)` and `sum_i E_i=R`. For all 388 pairs `(i,s)`, take natural slices `Q_i,s` with `Sub((D-1)E_i,Q_i,s)`. Define `U_s=sum_i Q_i,s` as expressions. Take five natural post streams `V_0,...,V_3,V_n`, with `Sub((D-1)R,V)` for each. Take one natural counter pre-stream `U_n`, with `Sub((D-1)E_0,U_n)`.

Chronology and counter equations are

```
b V_r + (H+a_r) = U_r + W f_r    (r=0,...,3)
b V_n + x = U_n
U_n = V_n + E_0.
```

The four row-update equations are

```
V_r + sum_(i,s:A_i[r,s]<0) (-A_i[r,s])Q_i,s
    + H sum_(i:c_ir<0) (-c_ir)E_i
  = sum_(i,s:A_i[r,s]>0) A_i[r,s]Q_i,s
    + H sum_(i:c_ir>0) c_ir E_i.
```

All displayed variable-length digit sums below are proof notation only. The emitted arithmetic uses fixed 97-way/four-way sums and the approved macros.

## 1. Masks and selectors have their exact intended meanings

Because `b>=256` and `h>=1`, the geometric equation implies

`R=1+b+...+b^(h-1)`.

The numbers `D` and `b` are powers of two and `D<b`. Thus the binary support of `R` consists of the lowest bit of each of its `h` base-b positions. The approved Sub theorem makes each selector exactly

`E_i=sum_(t=0)^(h-1) e_it b^t`, with `e_it in {0,1}`.

At every position the sum of these 97 bits is at most 97, strictly smaller than `b`. Therefore the selector sum has no carry. Its equality to `R` implies `sum_i e_it=1` at every position. There is exactly one branch `i_t` at each chronological position.

Likewise `(D-1)E_i` is the binary mask having all of the lowest `log2 D` bits in each selected position and zero bits elsewhere. There is no multiplication carry: it is precisely `sum_t (D-1)e_it b^t`. Consequently the slice condition is equivalent to

`Q_i,s=sum_t q_i,s,t b^t`, where `0<=q_i,s,t<D`, and `q_i,s,t=0` when `e_it=0`.

The one-hot property now shows, without a circular bound, that `U_s=sum_i Q_i,s` has digits `u_s,t=q_i_t,s,t<D` and no carry. It also shows that every slice is exactly the restriction of `U_s` to branch i's positions. No separate mask for `U_s` is necessary.

Each post stream similarly has exactly `h` available digits, all below `D`, and no nonzero digit above position `h-1`. The pre-counter mask gives the same bound and forces its digit to zero whenever the chosen branch is a TILE.

## 2. Chronology is literal, including both endpoints

Let `v_r,t` and `u_r,t` denote the bounded post and pre digits. Since `0<H+a_r<D<b`, neither side of the row chronology equation has any overlapping digit contributions. On the right, `U_r<W` and `f_r<b`, so the endpoint term occupies only digit `h`. Unique base-b expansion gives

```
u_r,0 = H+a_r
u_r,t+1 = v_r,t                (0<=t<h-1)
v_r,h-1 = f_r.
```

There is no reversal of time: lower base-b positions are earlier transitions. The counter equation, using `0<x<D<b`, gives the analogous chain, initial pre-counter `x`, and final post-counter zero. In particular the most significant counter post digit must vanish; it is not silently discarded modulo W.

Decode every row digit `u` or `v` as the signed integer `u-H` or `v-H`. This is a single canonical signed coordinate relative to the common H, with range `[-H,H-1]`; signed zero is the unique digit H. The representation does not use independently signed positive/negative parts. H itself need not be unique, and no finite-fold claim is made. The allowed boundary digit zero decodes to `-H` and is harmless.

The endpoint identities on the f's give exactly `X=Y` after transition h. The final counter is zero by its chronology equation.

## 3. No carries in the row equations

Fix one branch and row. Put

```
P=sum_s max(A_i[r,s],0)
N=sum_s max(-A_i[r,s],0)
c=1-P+N
M_ir=max(P,1+N).
```

Because exactly one branch is selected at each position, an arbitrary position's left-hand digit before carrying is at most

`L=(D-1)(1+N)+H max(-c,0)`,

and its right-hand digit is at most

`T=(D-1)P+H max(c,0)`.

Using `D=2H`, their maximum is exactly

`max(L,T)=(D-1) M_ir`.

For `c>=0`, `M_ir=1+N`, `L=(D-1)M_ir`, and `L-T=(H-1)c>=0`. For `c<0`, `M_ir=P`, `T=(D-1)M_ir`, and `T-L=(H-1)(-c)>=0`. This proves the bound for all `H>=1`, including H=1.

Moreover `2+P+N+|c|=2M_ir+1`. The proposed C therefore more than suffices to make every nonnegative digit on both sides strictly smaller than b. Each individual term is bounded by the corresponding whole side, so it too has no hidden carry. Equality of the packed integers is exactly equality at every digit. The decoded equation is

`v_r,t = sum_s A_i_t[r,s] u_s,t + H c_i_t,r`.

Subtract H and substitute `u_s,t=z_s,t+H` to get `z'_r,t=sum_s A_i_t[r,s]z_s,t`. This is the required fixed integral map, with canonical fixed signs. The sign split is on known integer coefficients; there is no selector-dependent sign test.

A sharper sufficient choice is any fixed power of two `C>=max(128,max M_ir)`. More directly it is enough to have a power-of-two b satisfying `b>max(97,D,(D-1)max M_ir)`. The existing choice is already valid, so changing it is optional.

Reading the 96 fixed tile pairs from the inert receipt in the right-action convention gives

```
max M_ir = 9255203311981004706447451614260
2 max M_ir+1 = 18510406623962009412894903228521
proposed rounded C = 2^104
sharper rounded C = 2^103.
```

The maximum occurs for tile_id 101, row 0, with coefficients `(-3299742864862636196661936795229,-5955460447118368509785514819030,0,0)`.

## 4. Exact counter transitions and chronological branch order

Each digit of `V_n+E_0` is at most D, strictly below b. Thus the packed counter update gives the scalar relation `u_n,t=v_n,t+e_0,t` at every position.

- At a LOAD position it gives `v_n,t=u_n,t-1`, with `u_n,t>=1` by nonnegativity
- At a TILE position the loader-only pre-mask already gives `u_n,t=0`; the update gives `v_n,t=0`

This is exactly the intended branch-specific counter relation on a natural accepting path. Chronology then forces every accepting branch word to be `LOAD^x TILE^d`, where `d=h-x>=0`. Before zero, a TILE is impossible. Once zero is reached, another LOAD is impossible because its post-counter would be negative. Therefore there are exactly x LOAD choices, with all of them before all TILE choices.

Restricting the packed counter to naturals loses no accepting signed-counter path from the predecessor formulation: its proved countdown argument already makes every such accepting path have this same shape. Its counters lie between x and zero.

## 5. Soundness and completeness

For soundness, take any positive integer witness assignment satisfying all expanded residuals. The approved macro theorems give the stated POWER/Sub relations. Sections 1-4 recover one branch and one pre/post state at every one of h positions, literal chronological joins, the exact signed initial rows and input counter, every required row and counter transition, and the specified endpoint. Hence the input has a genuine finite accepting countdown path. There is no modular wraparound, independently chosen row branch, disconnected multiset of edges, or uncharged sign choice.

For completeness, take a genuine finite accepting countdown path for positive x. It has h=x+d>=1 transitions and natural counters between zero and x. Choose a power-of-two H larger than every absolute row coordinate appearing in its finitely many states and large enough that `x<2H`. Then every offset row coordinate and every counter digit is below D=2H. Pack the pre/post digits in chronological order; let each E_i indicate the positions using branch i; let each Q_i,s be the indicated slice; and take the genuine endpoint offsets. The geometric, mask, chronology, counter, affine, endpoint and scalar bound equations all hold. The approved completeness of each POWER/Sub invocation supplies its fixed finite block of positive witness leaves. Thus the full polynomial certificate has a positive integer zero.

The case `d=0` remains included: all choices are LOAD, all tile selectors and their slices are zero, and the endpoint is tested after exactly x loads. The scalar mask semantics explicitly allow zero. No nonexistent TILE must be added for padding. The case `h=0` is intentionally omitted and is unnecessary for external positive x, since h>=x>=1. If the input contract were later enlarged to include x=0 and genuinely accepting empty total paths, that separate boundary would need explicit treatment; it is not claimed here.

## 6. Fixed arity, domain guards, and expansion boundary

The final design has exactly

- 97 selector Sub calls
- 388 slice Sub calls
- 5 post-stream Sub calls
- 1 loader-only pre-counter Sub call

for 491 Sub calls. Their three POWER calls each plus the two direct powers H and W give 1475 POWER calls. b is a source expression `CD`, not an additional POWER output. There is no AND or SPREAD call. All of these counts are independent of h, x, H, and the state magnitudes.

Every Sub mask/value is natural before its theorem is applied. H and W have base at least two and natural exponents; h is in fact positive. `D-1` and `b-1` are natural. R and the stream/slice/selectors are declared natural, so the geometric equation is used only in its proper domain. The input bounds and four endpoint bounds can be implemented by positive slacks, and `H>max|a|` by one positive slack above the fixed maximum. These inequalities must really appear in the final residual list.

Natural witness values use independent positive leaves minus one; positive duration and strict slacks can use positive leaves directly. The external input is already the literal positive x and must retain its declared input convention, rather than being accidentally replaced by x-1 during witness adaptation. All fixed coefficient signs and constants remain fixed integer literals.

There are finitely many fixed-width source expressions and fixed blocks of macro auxiliaries. Expanding every approved macro, expressing scalar guards by slack equations, and summing the squares of all residuals therefore yields one fixed-arity integer polynomial. Over positive integer assignments its zero set is exactly the accepting input relation. This review does not assert a real-witness equivalence, finite-foldness, a minimal number of variables/operations, or an exact degree or gate count for a DAG not yet inspected.

## 7. Relation to the earlier AND proposal

Under the one-hot selector masks, every current slice satisfies `Q_i,s=AND(U_s,(b-1)E_i)`. Conversely the earlier bounded U and exact-AND slices satisfy the current slice masks and `U_s=sum_i Q_i,s`. The new pre-counter mask is equivalent to the earlier whole-counter mask together with vanishing on tile positions, and the counter update supplies the post TILE guard. Thus the smaller construction is semantically equivalent to the original packing while eliminating the AND layer and the independent pre-row streams.

No mathematical defect was found in the final slice-only variant. Implementation review should verify all scalar guards, the matrix transpose convention, every selector/slice mask, the raw input convention, and inclusion of every residual in the final sum of squares.
