# Exact regrouping of the U9 mask and history units

The [compiler](neary_woods_universal_history_unit_partitions.py) searches every
partition of the integer factors after the three
[260-operation history/mask rewrites](neary_woods_universal_history_units260.md),
with the [lower-history unit](neary_woods_universal_lower_unit259.md) optional.
It covers all sixteen inherited strong-normalization/positive-scale bases.
This improves three propagated degree bounds at unchanged operation counts:

| Operations | Previous bound | New bound | Positive witnesses |
|---:|---:|---:|---:|
|266|1108|1106|44|
|267|1062|1060|44|
|268|740|738|44|

The smallest operation count remains **259=133M+126A**, with43 positive
witnesses and degree at most3861. The minimum degree bound in the searched
family remains608 at270 operations and44 witnesses. Unlike the predecessors'
placement searches, the new search may move every old and new factor between
groups. Its optimality claim concerns this finite family and its propagated
degree objective. It does not prove a minimum exact degree or a global
arithmetic lower bound. The separate75/87 frontier is unchanged.

The [receipt](neary_woods_universal_history_unit_partitions.json) records the
selected actual gate schedules, every best-by-group-count ledger and the
finite subset-search statistics. The ordinary input, actual fixed U9 machine,
four positive program parameters and paid initialization counter are retained.
The separate fifth duration-bound interface is checked as well.

## 1. Fixed bases and the positive solution relation

Start with each of the sixteen native bases from the
[computed-port partition theorem](neary_woods_universal_computed_ports_partitions.md):
independently normalize the two strong equations and independently use the
two positive-scale projections. Apply the frozen factored-port and shared
history identities, then the mask, upper-history and global-history units.
Finally either retain the lower transport as an ordinary comparison or use
its proved unit. This gives32 fixed arithmetic bases per program-bound
interface, with43,44 or45 positive witnesses.

Each canonical base initially puts all its factors into a single product.
On a complete positive zero on a valid program/input slice, **every individual
factor equals1**, and every ordinary residual is zero. For the retained-lower
bases this is the sign proof of260, including both independently recovered
native indices. For the absorbed-lower bases the259 proof first recovers the
same typing and upper chronology, excludes the corrupted sentinel V0-2, then
forces the global sign. Ordinary strong comparisons remain where the base
has not normalized that core. None of these sign arguments requires a
particular partition of the factors.

Partition the full factor list into nonempty groups with products G_j. Two
allowed finalizers are

    sum_i r_i^2 + sum_j (G_j-1)^2,                    (1)

or, for one distinguished anchor a,

    G_a * (1 + sum_i r_i^2
                 + sum_(j!=a) (G_j-1)^2) - 1.        (2)

Every quantity is an integer. In(2), the parenthesized value is a positive
integer. A zero forces that value and G_a both to1; all its squared terms
then vanish. Thus either finalizer forces every group product to1 and every
ordinary residual to0. Multiplying the groups gives the original single
product1, and hence a positive zero of the canonical base. Its individual
factor sign theorem now applies. Conversely a canonical positive zero makes
every factor1, so it satisfies every partition and either finalizer.

Therefore regrouping preserves the **entire positive zero set within one
fixed base on valid program/input slices**. No change of supplied coordinates
is involved in regrouping. Across different native bases, retain their
inherited projections and, where required, fresh canonical auxiliary lifts;
no all-coordinate bijection between those bases is claimed. The lower-unit
option still requires the valid encoded input; it does not acquire an
all-parameter equivalence from this search.

## 2. Literal costs, including the empty residual case

Let c be the number of gates in the closure of all individual factors and
ordinary comparisons, n the number of factors, m the number of ordinary
comparisons, and g the number of groups. Forming the groups costs n-g
multiplications. Their comparisons and either standard finalizer then give

    polynomial operations = c+n+3m-1+2g.             (3)

This formula includes every squared residual and each multiplication by a
nonunit fixed numeral. The source retains only the needed factor/ordinary
closure before emitting new products, so historical product gates are not
counted or executed after regrouping.

There is one special case: m=0,g=1 with an anchor. The literal polynomial is
just G_0-1, with no artificial square, addition to0 or multiplication by1.
Its cost is **c+n**, one less than(3). This is exactly the259 endpoint.
The compiler handles this case explicitly. Its degree calculation passes a
zero residual only to the frozen degree propagator; the literal source has
no such comparison. Every emitted gate reaches its actual final output.

Within a fixed base and fixed g, the two finalizers otherwise have the same
operation count. The exceptional one-group anchor also has lower degree
than the one-group SOS, because every factor degree bound is positive.
Consequently minimizing degree for each g, then comparing actual costs,
loses no cost/degree alternative in this family.

## 3. The exact finite objective and exhaustive search

Use the inherited propagated degree weights w_i of the actual factor gates
and let r be the maximum bound on an ordinary residual, or0 if none remains.
The only special algebraic cancellation is the already guarded exact main
Pell norm expansion; no equation holding only at zeros reduces a degree.
For a group let d_j=sum_(i in group j) w_i. The objectives are

    SOS:       2 max(r,d_0,...,d_(g-1));
    anchor a:  d_a + 2 max(r, all d_j with j!=a).       (4)

For each factor subset S and group count k, define

    F(S,k) = minimum possible maximum group weight
             over partitions of S into k nonempty groups.

The reused [subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.py)
computes this exactly. Its recurrence selects every possible first group
containing the least element of S and recurses on its complement. This
removes group-order duplicates without omitting a partition. The base cases
are one group, all singleton groups, and F(empty,0)=0.

Greedy grouping supplies only an initial upper bound. Pruning uses the
proved lower bound max(largest remaining weight, ceiling(total/k)), or a
first-group weight already unable to improve the incumbent. The anchor
search enumerates every possible nonempty anchor subset A; for its remaining
k-1 groups the objective depends only on F(S minus A,k-1). It also considers
an unanchored SOS for every k. These steps exhaust(4), including r=0.

The search is rerun after all new unit factors have been added, for both
lower treatments and all sixteen bases. Every chosen partition is compiled
and its actual operation ledger and guarded degree propagation are checked
against(3)--(4). The two program-bound interfaces have separately emitted
sources and equal reported ledgers. The final frontier discards a row only
when another row has no larger operation count and no larger degree bound.
Witness-specific frontiers are also retained rather than silently treating
an extra witness as free.

## 4. Results and the new balanced partitions

The combined operation/degree frontier is

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|259|3861|43|
|261|3450|43|
|262|3404|43|
|263|2286|44|
|264|1518|44|
|265|1472|44|
|266|1106|44|
|267|1060|44|
|268|738|44|
|269|708|44|
|270|608|44|

There is no260 row:259 has both fewer operations and a smaller bound.
The fixed43-witness frontier additionally gives263/2380 and265/1810 before
267/1344. The fixed45-witness frontier ends at273/608; the complete lists
are in the receipt. A slash here separates operation count and degree bound.

At266 the new SOS partition balances the two group weights at553 and553,
with maximum ordinary residual degree206, hence degree bound1106. At267
its two weights are530 and530, giving1060. At268 the three weights are
368,369,369, giving738. The266 and268 bases normalize only the geometry
strong equation and use only its positive-scale projection;267 normalizes
neither strong equation and uses the same geometry scale projection.
All three retain the lower transport comparison. Their exact polynomial
ledgers are respectively134M+132A,133M+134A and134M+134A. These three
within-base optima also have short independent certificates: an SOS bound
is at least twice the ceiling of total factor weight divided by the group
count, attained by the displayed balances. With two or three groups, an
anchor bound is at least the total factor weight and cannot improve them.

The improvement is possible because some old factors move between groups;
placing only the new factors into inherited selected partitions cannot
reach these balances. Absorbing the lower comparison is useful for259 but
is optional for the lower-degree alternatives. Keeping it is not an unpaid
constraint: its literal residual and square remain in those polynomials.

## 5. Reproduction and limits of the finite evidence

```sh
python3 neary_woods_universal_history_unit_partitions.py
```

The writer and fresh default recompute32 searches and928 emitted ledgers,
with44 selected full schedules across both program-bound interfaces.
There are172 whole-source audit contexts, checking1,376 complete output and
retained-register identities,688 with signed assignments. These include
both finalizers even when only one is selected by the degree objective.
An independent Bell-partition enumeration checks21 small weighted problems,
including zero ordinary residuals, through15,882 partition/anchor choices.
This validates the subset optimizer against a different exhaustive method.

Arbitrary-point tests compare each actual polynomial with a separately
assembled scalar finalizer. They do not assert equality between different
partitions away from their zero sets. Nor do they materialize enormous
universal Pell witnesses. Positive equivalence follows from Section1 and
the complete parent theorems. The optimization is an exact finite integer
calculation of the stated upper-bound objective, not a formalization of
all mathematics or a search over all possible Diophantine circuits.

Author writer and fresh default replay pass. Franklin independently reviewed
the full proof, literal source and subset recurrence and passed a fresh
default replay with no findings. His own executor checked512 complete
outputs/group products/retained-register identities,256 signed, across all32
bases and both program-bound interfaces, with128 output closures. A separate
restricted-growth Bell enumerator checked21 new weighted problems through
15,882 partition/anchor choices; the displayed balanced optima also passed
his direct lower-bound proof. All six local links resolve. Source and receipt
are frozen; no frozen parent or shared navigation is changed by this packet.
