# Grouping identical upper-row choices in the directed193 countdown compiler

The complete saved local tile predicate costs **2015 = 1103 M + 912 A**, and its ordinary-input countdown extension costs **2041 = 1115 M + 926 A**. Each saves **24 additions** against its immediate parent. Both complete instruction arrays are emitted in the companion receipt, and every computed instruction is live.

This is an exact equivalence of local zero sets over the reals, hence also over signed integers. It is **not equality of the parent and child polynomial values**. Their arbitrary-length transition relations and ordinary-input semantics are unchanged, while encoding arbitrary duration with a fixed number of Diophantine witnesses remains unpaid. The current universal 84-operation representation is unaffected.

## 1. Authenticated actual source

The checker reads only the frozen [synchronized-row packet](matrix193_synchronized_rows.md) and [countdown packet](matrix193_countdown_rows.md) as inert bytes. It imports or executes no predecessor Python. Exact dependency pins are:

| File | SHA-256 |
|---|---|
| `matrix193_synchronized_rows.py` | `da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52` |
| `matrix193_synchronized_rows.json` | `9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233` |
| `matrix193_synchronized_rows.md` | `ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2` |
| `matrix193_countdown_rows.py` | `5a1d373933f43b9f94dc54cf276aaa865fc6c82a1a25082842d8d4690e668577` |
| `matrix193_countdown_rows.json` | `f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0` |
| `matrix193_countdown_rows.md` | `93363ca2f21949e2c7fa6d2bd4052b2219ec06fe4c2d52ba317fc19a229c5361` |

Each of the actual 96 tiles supplies integral determinant-one matrices K_i,G_i acting on row vectors. The signed supplied state ports are X=(x0,x1), Y=(y0,y1), X',Y'. The intended tile transition is

    X' = X K_i,   Y' = Y G_i.

There are exactly 72 distinct K matrices and 96 distinct G matrices. The K-group sizes are 56 singletons, 9 pairs, 6 triples, and 1 quadruple, totaling 96 original choices. These 72 polynomial factors do not mean that the transition alphabet has shrunk to 72 choices.

Define the two nonnegative quadratic forms

    A_K = ||X' - X K||^2,
    B_i = ||Y' - Y G_i||^2.

Here each norm means exactly the sum of the two displayed scalar squares. All fixed matrix coefficient multiplications in these forms are charged, using the parent's fixed-numeral convention. Ordinary input and witness ports are not silently added.

## 2. Exact zero relation from nonnegativity

The parent's polynomial is

    P_old = product_i (A_K(i) + B_i).

For each distinct K let I_K be precisely the set of original tile identifiers having that K, and define

    Q_K = A_K + product_(i in I_K) B_i,
    P_grouped = product_K Q_K.

Every A_K and B_i is nonnegative for every real tuple. So is every Q_K. The following equivalences hold without any trajectory, matrix-group, integrality, or zero-only assumption:

    Q_K = 0
      iff A_K = 0 and product_(i in I_K) B_i = 0
      iff there is i in I_K with A_K = B_i = 0.

Taking the product over K shows that `P_grouped=0` is exactly the same 96-way synchronized transition relation as `P_old=0`. Synchronization is retained: the chosen G_i is restricted to the identifiers in the matching K group. Arbitrary independent choices of K and G are not allowed.

This uses the ordered-field nonnegativity of squared real residuals. It is not a polynomial identity: at formal nonnegative values A=1 and B_1=B_2=1, the old two-branch product is 4 and the grouped factor is 2. Neither equality of off-zero values nor equality of complex zero sets is claimed.

## 3. Complete arithmetic schedules and exact degrees

The new builder reconstructs the literal affine residuals from the actual matrix table. It shares identical arithmetic registers and omits only fixed zero/one operations according to its explicit schedule. It saves all upper/lower residual wires, lane norms, group products, group sums and the full outer product.

For a K group of size d, the old four-square branch finalizers require 2d additions after their common upper two-square sum. The new organization uses d lower two-square sums and one group sum, giving d+1 such additions. The saving is d-1. The internal lower products cost d-1 multiplications; summing across all groups and adding the 71 outer multiplications gives

    sum_K (|I_K|-1) + (72-1) = 24 + 71 = 95,

the same number as the old 96-factor final product. Consequently the total addition saving is `96-72=24`, with no multiplication change. The independently recounted complete source confirms:

| Complete local predicate | Parent M/A/total | New M/A/total | Exact degree |
|---|---|---|---:|
| Four-coordinate tile relation | 1103 / 936 / 2039 | **1103 / 912 / 2015** | 192 |
| Five-coordinate countdown relation | 1115 / 950 / 2065 | **1115 / 926 / 2041** | 194 |

A group of size d has degree at most 2d, so P_grouped has degree at most 192. To prove attainment on the actual whole DAG, set only `next_y0=t` and all other supplied ports to zero. Then every A_K is zero and every B_i is t²; thus every group is t^(2|I_K|), and

    P_grouped = t^192.

The former next-x degree line is not reused: on that line this grouped polynomial instead has degree 144. The change in off-zero degree along individual lines is compatible with preserving the full degree and real zero set.

The helper independently expands all 336 distinct scalar residuals and all 72 complete group factors against the matrix formulas, checking 2,096 factor coefficients. It separately checks that the outer finalizer multiplies every group exactly once and that their member lists partition all original 96 tiles. A complete univariate interpretation, rather than a syntactic guess, verifies the degree line above. The degree upper bound is also propagated through every paid gate.

## 4. LOAD versus TILE remains exact

The five-coordinate source keeps the inherited loader, with the actual fixed matrix

    B^(-1) = [[52891,-29036],[94920,-52109]].

Let n,n' be signed real counter ports. Its loader error is

    E_load = ||X'-X||^2 + ||Y'-Y B^(-1)||^2 + (n-n'-1)^2.

Replace only the old tile output by P_grouped in the inherited 26-instruction extension:

    E_tile = P_grouped + n^2 + (n')^2,
    P_count = E_load * E_tile.

The helper checks the literal parent prefix identity and retains those 26 operations with the needed wire renaming. It then proves their complete formal expression, including all 62 coefficients, using an independent symbolic port for P_grouped. The original seven-gate endpoint `(x0-y0)^2+(x1-y1)^2+n^2` and zero-gate initialization are copied unchanged into the receipt.

All three displayed quantities are nonnegative on every real tuple. A local zero is therefore exactly either the original loader transition, or one original synchronized tile transition with **both** n=n'=0. This remains true for arbitrary real n, not just integral or nonnegative counters. Loader and tile branches are disjoint because their required next counters differ at n=0.

On the degree line of Section 3, E_load=t²+1 and E_tile=t^192. The complete new countdown DAG therefore equals

    t^194 + t^192,

proving exact degree 194 without substituting any on-zero constraints.

For any finite path from initial counter x to endpoint counter zero, each LOAD reduces the counter by one and TILE leaves it zero. Exactly x loads must occur. Every tile occurs after those loads, and a later load would prevent the endpoint counter from being zero. Hence the full accepted word is still `LOAD^x TILE*`, even with signed real counter witnesses. For integer x and integral initial rows, every chosen affine transition has integral coefficients and preserves integrality, so all states in a real zero trajectory are integral. The original row-injectivity and semigroup-word arguments then apply unchanged. No new group-membership, exact Pell-index, phase, or nonnegativity oracle is required.

## 5. Fixed-duration implications and remaining scope

For fixed total duration h>=1, copy the complete 2041-gate countdown predicate at each step and add its h nonnegative outputs and the seven-gate endpoint. With the fixed initial rows and n=x directly substituted, this gives the explicit upper bound

    2042h + 7 gates,   5h signed witnesses,   degree at most 194.

The 24h-gate improvement is measured against the parent's copied-schedule bound `2066h+7`. The local exact degree is not asserted after arbitrary initial substitutions. For the four-coordinate synchronized interface with an already supplied target row, the corresponding bound is `2016d+5` with 4d signed witnesses and degree at most 192. Adding the parent's conditional three-gate target assembly gives `2016d+8`; its exact input-index obligation remains, which is why the countdown version is useful.

These counts are for the saved fixed-context matrix table. Grouping identical K matrices is a valid compiler transformation for any table, but the 72-group inventory and the numerical saving are not asserted for every arbitrary program context. The inherited effective fixed-program semantic recipe is unchanged. The particular saved fixture is not promoted to a compiler for every c.e. language.

The checker also inventories duplicate scalar affine residuals: their distinct counts are 72,72,96,96. Both upper-coordinate equality partitions coincide with the K partition; every lower scalar residual is unique. Thus this actual table exposes no additional nested factoring of literally repeated scalar residuals beyond these groups. This is a finite source inventory, not a lower bound against different algebraic, coordinate, or selector constructions.

Unbounded trajectory packing, a fixed witness count for arbitrary length, signed-value bounds in that packing and conversion to a positive-witness interface remain unpaid. This packet neither weakens those obligations nor claims an improved complete universal polynomial.

## 6. Bounded evidence and replay

The receipt stores both complete instruction arrays, every grouping and transition matrix, the copied initializer/endpoint interface, exact ledgers and degree certificates. In addition to the coefficient proofs, 228 whole-source signed/rational checks cover every tile in both predicates, four loader examples including a nonintegral counter, and sixteen arbitrary tuples in both predicates. These finite examples supplement the real-zero proof; they do not prove arbitrary-length simulation by extrapolation. Existing long accepting traces are inherited rather than rerun.

Use the bounded CLI against the directory containing the six pinned parents:

    python3 matrix193_grouped_row_choices.py --root /absolute/native-stream-queue --expect matrix193_grouped_row_choices.json
    python3 -O matrix193_grouped_row_choices.py --root /absolute/native-stream-queue --expect matrix193_grouped_row_choices.json

`--output` instead writes a new receipt to a nonexistent path. Checks use explicit exceptions and remain enabled under optimized Python. JSON duplicates/nonfinite values are rejected, and receipt comparison preserves exact generated bytes and types. No maintained general public compiler API is claimed.
