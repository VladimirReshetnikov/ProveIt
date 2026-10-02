# Exact grouped asymmetric tradeoffs:91/104,93/72 and95/64

The [source](complete75_asymmetric_factor_partitions.py) gives three new
complete universal degree tradeoffs, with the same19 strictly positive
witnesses and ordinary positive input as the
[asymmetric87/88 construction](complete75_asymmetric_scale_tradeoffs.md):

| Polynomial operations | M | A | Exact degree | Certificate operations | Equations |
|---:|---:|---:|---:|---:|---:|
|87|48|39|169|86|1|
|88|47|41|125|87|1|
|**91**|48|43|**104**|83|3|
|**93**|48|45|**72**|82|4|
|**95**|48|47|**64**|81|5|

The first two rows are the unchanged asymmetric parent endpoints. The
last three retain the full ordinary strong equation as a separate
comparison and group the remaining seven factors into sums of squares.
Every row is a representation of the same computably enumerable input
set on the unchanged valid fixed-program slice. No program parameter,
input encoding, compiler numeral or positive domain is altered.

This is the exact operation/degree frontier within the three finite
source families specified below. It is not an optimum over other
circuits, coordinate changes, factors or universal representations.
In particular64 is a degree floor only for this grouping family, and
the separate best comparison-certificate operation bound remains75.
The [receipt](complete75_asymmetric_factor_partitions.json) records all23
best-by-group-count ledgers and the five selected complete sources.

## 1. Three guarded factor bases

All bases retain X=wq and Y=sq³, and every other definition of the
asymmetric parent. Write N0,N1,N2,N3,Nk,Nt,Ns,L for its eight factors,
in that order. The full source guards reconstruct the selected parent
before pruning only ancestors unused by the declared factors and
retained comparisons.

| Base | Factor weights, in order | Core gates | Retained ordinary residual | Its exact degree |
|---|---|---:|---|---:|
|Normalized units|12,18,32,56,7,3,34,7|79|none|0|
|Ordinary units|12,18,32,24,7,3,22,7|80|none|0|
|Ordinary comparison|12,18,32,24,7,3,7|78|`Qs=(ic²)²−Delta(f²−1)`|22|

The last base omits Ns, so its order is N0,N1,N2,N3,Nk,Nt,L.
For the ordinary source the exact identity is **Ns=1+Qs**. Its source
already computes both sides of Qs; replacing its unit factor by this
comparison deletes only the two additions `strong_difference` and
`norm_strong` from the factor core. The literal strong square and
Delta(f²−1) are still evaluated and compared. The change is not a weak
strong-norm or rank condition.

The asymmetric theorem gives a full positive-zero bijection to each
respective frozen87 or88 source. Those complete parent proofs show that
**every individual factor equals+1 at every positive zero** under the
actual compiler hypotheses. This remains true after the asymmetric
coordinate map because all factor values agree exactly. Thus, within
each base, imposing all its factors equal1 and all its retained
comparisons is equivalent to the parent's entire positive zero set.
In the ordinary-comparison base this uses Ns=1+Qs in both directions.

Across normalized and ordinary strong treatments the accepted-input
projections agree through the inherited auxiliary construction; no
bijection of supplied tuples across those treatments is claimed.
The current grouping transformations, within one treatment, change no
supplied coordinate at all.

## 2. Complete grouping and finalizer semantics

Partition all factor indices into g nonempty disjoint groups and let
G_j be each group's product. Every factor occurs exactly once. There
are two allowed finalizers. With Q_l the retained ordinary residuals,
the sum-of-squares form is

    sum_l Q_l² + sum_j (G_j−1)².                       (1)

Alternatively distinguish one group a as an unsquared anchor:

    G_a * (1+sum_l Q_l²+sum_(j!=a)(G_j−1)²)−1.         (2)

Every integer zero of(1) has each displayed residual zero. Every
integer zero of(2) also does: its nonnegative integer sum S obeys
`G_a(1+S)=1`, so G_a=1 and S=0. In either case multiplying the group
equalities gives the full original factor product equal1. Together
with the retained Qs where present, this restores exactly the parent
positive zero. Conversely, at every parent positive zero all individual
factors are+1 and all retained comparisons hold, so every grouping
vanishes. This proves **identical full supplied positive zero sets
within each base**, not just soundness or canonical completeness.

Groups are formed only with binary multiplication. If a base has C core
gates, n factors and m retained comparisons, its group products cost
n−g additional gates. Both general finalizers cost3(m+g)−1 further
gates. Thus their complete operation count is

    C+n+3m+2g−1.                                     (3)

There is one literal exception: if m=0,g=1 and the single group is the
anchor, (2) is simply G_0−1, using one subtraction. Its total is C+n,
one less than(3). This is the existing87 or88 product source, not a
new free finalizer or comparison. The checker handles this empty
residual case explicitly. The SOS one-group alternative costs one more
and has twice the degree, so it cannot improve a frontier endpoint.

Every emitted factor-core gate reaches a group or retained comparison;
every grouped source gate reaches the selected complete output. The
source APIs reject changed core rows, factor degrees or comparisons,
missing/duplicated factor indices, invalid anchors and stale group
register exports.

## 3. Exact degree objective and finite search

The factor weights in Section1 are **exact degrees**, with the nonzero
leading homogeneous forms proved in the asymmetric source. Qs also has
exact degree22: its (ic²)² term has that degree and its other term has
degree14. Products have degree equal to the sum of their factor degrees,
since the polynomial ring is an integral domain. A sum of squares has
degree twice the largest residual degree: its leading squares cannot
cancel over the reals. Likewise the nonconstant positive-sum term in(2)
has that exact degree, and multiplying by the anchor adds its exact
degree. In the empty case, subtracting1 does not change the nonconstant
anchor's degree.

Let w_i be the factor weights, r the maximum original residual degree
(or0), and s_j=sum_(i in group j)w_i. The exact objective is therefore

    SOS:       2 max(r,s_0,...,s_(g−1)),
    anchor a:  s_a+2 max(r,{s_j:j!=a}).                (4)

No zero-set substitution or unproved cancellation is used in(4).
All compiler numerals have degree zero, as in the parent; x and all19
supplied witnesses have degree one.

The [reused subset optimizer](neary_woods_universal_joint_and_coupled_partitions.md)
computes the least possible maximum group weight for each subset and
number of groups. Its recurrence enumerates a first group containing
the least remaining index, then partitions the complement. This removes
permutation duplicates without excluding any partition. The SOS
objective uses the optimum for all factors. For an anchor it enumerates
every nonempty distinguished subset, adds its weight, and optimizes the
remaining groups' maximum. Thus all disjoint partitions, all anchors
and the SOS competitor are covered for every g.

A separately implemented restricted-growth Bell enumeration checks the
complete objective here, without using the subset-DP helper. It visits
4,140 partitions for each eight-factor base and877 for the seven-factor
base: **9,157 partitions and46,434 SOS/anchor choices** in total. The
exact minima by group count are

| Base | g=1 |2|3|4|5|6|7|8|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|Normalized units|169|170|114|112|112|112|112|112|
|Ordinary units|125|126|84|64|64|64|64|64|
|Ordinary comparison|147|104|72|64|64|64|64|—|

The operation formula(3), including its stated exception, gives precisely
the five operation/degree frontier rows in the opening table. This
frontier compares operation count and degree; it does not assert
simultaneous optimality in certificate size or equation count. For
example the ordinary eight-unit base also gives95/64 with84 certificate
gates and four equations, using four SOS groups. The selected ordinary
comparison row uses81 certificate gates and five equations.

The unrestricted-group floors in the three bases are112,64,64. The
checker separately considers every distinguished anchor subset
(255,255,127 choices), with all remaining factors allowed as singletons,
and compares against the SOS singleton bound. Every resulting lower
bound is at least the claimed floor, which is attained in the table.
This is a finite factor-family certificate, not a general lower bound
for universal polynomial degree.

## 4. The three new complete schedules

For the ordinary-comparison base, use its seven-factor order
N0,N1,N2,N3,Nk,Nt,L and retain Qs=0 throughout.

* **91/104:** groups `(N1,N3,Nk,Nt)` and `(N0,N2,L)` have degrees52
  and51. Their two product-minus-one squares plus Qs² give degree104.
* **93/72:** groups `(N0,N3)`, `(N2,Nt)` and `(N1,Nk,L)` have degrees
  36,35,32. The four residual squares give degree72.
* **95/64:** groups `(N2)`, `(N3)`, `(N0,Nk,Nt)` and `(N1,L)` have
  degrees32,24,22,25. Their four residual squares plus Qs² give degree64.

The unexpected72 rather than70 at93 has a short exact certificate.
The seven weights sum to103. Three groups of maximum35 would force
at least33 in every group. The weight32 must be paired with3: otherwise
its group is32 and the remaining71 cannot fit in two groups of size35.
After pairing32+3, the group containing24 can add one7 to reach31, or
two7s to reach38, while12 or18 already exceed35. It cannot reach the
required interval[33,35]. Thus cap35 is impossible, and the displayed
cap36 partition is sharp. Two groups have peak at leastceil(103/2)=52,
attained by the91 construction; every SOS grouping has peak at least32,
attained by the95 construction.

The exact search also includes anchors, all group counts and the two
other strong bases. No claim that the three short SOS arguments alone
settle those larger alternatives is needed.

## 5. Executable checks and scope

Run

    /tmp/diophantine-research-venv/bin/python complete75_asymmetric_factor_partitions.py

for a fresh receipt comparison; `--write` regenerates it. The checker
emits all23 best-by-group-count ledgers and all five frontier sources,
checks source liveness and literal opcode counts, and verifies30 malformed
base/plan/successor rejections. On24 assignments for each selected plan,
half signed, it checks552 complete core/register/manual-finalizer
identities, including276 signed cases. It also replays each factor core
against the frozen cubed-X parent through the asymmetric rational
coordinate map, preserving the explicit distinction between off-zero
rational replay and on-zero positive integer restoration.

Ten weighted univariate expansions check every factor and group degree
and attain the asserted exact complete degree for the five frontier
sources. These corroborate the general leading-form and sum-of-squares
proof, rather than replacing it. The Bell audit covers every finite
partition objective, not every possible arithmetic circuit. No numerical
fixture here is claimed to materialize a complete universal Pell zero.

Author receipt generation and a separate fresh default replay passed. All
four local links and whitespace checks pass.

An independent full proof/source/dependency review and fresh replay passed
without findings. It rechecked within-base full positive-zero equality,
Ns=1+Qs, exact SOS/anchor degree and the empty finalizer. Its separate
enumerator reproduced all9,157 partitions and46,434 cost/degree choices
and the complete frontier. Additional independent checks passed71 emitted
opcode/liveness ledgers (all23 winners and48 new ordered/anchor plans),
568 complete core/cubed-parent/manual-output identities (284 signed),
23 exact all-winner degree slices and301 cap35 obstruction cases. These
are finite source/objective checks, not full compiler-zero fixtures.

Root also reviewed the complete source and proof and replayed the receipt;
all passed without findings.
