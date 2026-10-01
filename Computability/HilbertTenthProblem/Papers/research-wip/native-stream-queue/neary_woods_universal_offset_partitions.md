# All factor partitions for the shifted-offset U9 polynomial

The [literal compiler](neary_woods_universal_offset_partitions.py) extends
the [258-operation construction](neary_woods_universal_offset258.md) from
selected mapped schedules to every disjoint factor partition and either
allowed finalizer, over all sixteen native bases. Four conservative degree
bounds improve at unchanged operation counts:

| Operations | Previously selected bound | New bound | Positive witnesses |
|---:|---:|---:|---:|
|265|1114|1112|44|
|266|1068|1066|44|
|267|744|742|44|
|268|716|712|44|

The minimum operation count is still **258=133M+125A**, with43 positive
witnesses and degree at most3861. The minimum degree bound in this finite
family remains608 at269 operations and44 witnesses. The ordinary input,
actual fixed U9 machine and four positive program parameters are retained.
The separate fifth duration-bound interface has the same reported ledgers.
The overall75-certificate/87-polynomial bounds are unchanged.

This packet uses the **new** offset meaning E'=E-1 throughout. The
[older history-unit partition search](neary_woods_universal_history_unit_partitions.md)
retains E and is a separate family. No polynomial identity is asserted
between the two parameter conventions at identical numerical parameters.
The [receipt](neary_woods_universal_offset_partitions.json) records every
best-by-group-count ledger and the selected full literal sources.

## 1. The affine change commutes with every grouping

Start with a canonical old-offset base with the lower-history comparison
absorbed. Independently choose which of its two strong equations are
normalized and which two positive-scale projections are used. Apply the
guarded258 rewrite **before** regrouping. This gives sixteen shifted bases.
Each factor is an integer polynomial. On a positive zero of a canonical
shifted base on a valid program/input slice, every factor is1 and all its
remaining ordinary residuals vanish, by the full258 sign and loader proof.

For any partition of those factors into nonempty groups G_j, use either

    sum_i r_i^2 + sum_j (G_j-1)^2,                       (1)

or, with one distinguished group a,

    G_a*(1 + sum_i r_i^2 + sum_(j!=a)(G_j-1)^2) - 1.     (2)

All quantities are integers. In(2), the parenthesized factor is a positive
integer. A zero forces it and G_a both to1, and hence all its squared
residuals vanish. Thus either finalizer forces all group products1 and all
ordinary residuals0. Multiplying group products recovers the canonical
single product1. The canonical sign theorem then gives every individual
factor1. Conversely a canonical positive zero satisfies every regrouping.

Regrouping therefore preserves the entire positive zero set within each
fixed shifted base on valid program/input slices. Across native bases,
use their proved projections and fresh canonical positive extensions;
an all-coordinate bijection is not claimed.

The exact affine map from the shifted source to its old-offset parent is

    E_old=E_new+1,
    height_gap_old=height_gap_new-1,
    duration_gap_old=duration_gap_new-1  (merged bound only).       (3)

The last coordinate is unchanged with a separate bound. The258 theorem
proves that all individual unit factors and ordinary residuals are equal
under(3), on arbitrary integer assignments. Consequently any products,
squares and sums of those expressions agree, including(1) and(2). This
proves the complete polynomial identity for **matching** partitions and
finalizers. The active parent metadata is explicitly replaced by the
same regrouped parent; leaving its canonical parent there would describe
the wrong arbitrary-point polynomial.

Map(3) can send a positive height gap1 to0. Soundness uses the direct258
valid-slice proof, not a positive inverse assumption. For completeness,
start with a canonical old positive zero and use the inverse of(3).
The valid sentinel recipe guarantees E_old-1>0, and both affected gaps
increase by1. This gives a positive shifted zero, whose individual
factors are1 and which therefore satisfies every chosen partition.
No ordinary-input recoding or extra existential coordinate is introduced.

## 2. Literal costs and the exact finite search

Let c count the source closure of individual factors and ordinary
comparisons, n count the factors, m count the ordinary comparisons and
g count the groups. Their literal polynomial cost is

    c+n+3m-1+2g,                                         (4)

except when m=0,g=1 and the single group is anchored. That case emits
only its product minus1 and costs c+n. The one-addition saving of258 is
in the factor closure, so it persists for every partition and finalizer.
Both finalizers otherwise have the same cost at fixed g. The exceptional
one-group anchor also has smaller propagated degree than its SOS.

The compiler discards historical product rows, emits the selected group
products, checks source closure and counts the actual source. Every
reported shifted ledger costs exactly one operation less than its
matching old-offset absorbed-lower ledger. Complete propagated degree
dictionaries agree under the affine change. They retain the inherited,
guarded main-Pell-norm cancellation and include program coordinates.

For actual factor degree bounds w_i and maximum ordinary residual bound r,
write d_j=sum_(i in group j)w_i. The finite objective is

    SOS:       2 max(r,d_0,...,d_(g-1));
    anchor a:  d_a + 2 max(r, all d_j with j!=a).          (5)

The inherited [exact subset optimizer](neary_woods_universal_joint_and_coupled_partitions.py)
is rerun on all sixteen shifted bases. For a subset S and k groups, its
recurrence minimizes the maximum group weight over every first group
containing the least element of S, then partitions the complement.
Only proved largest-weight and average-weight lower bounds prune branches;
a greedy partition supplies an upper bound. The anchor search enumerates
every nonempty anchor subset and solves the complementary groups exactly.
It also considers SOS. Thus every partition/finalizer is represented in
the optimization of(5), although redundant group orderings are suppressed.

Every chosen plan is compiled independently, and its degree propagation
is checked against(5). Costs and degrees are then compared to give the
Pareto frontier. Witness-specific frontiers are retained as well. This
proves optimality for this **finite propagated-bound objective**, not
exact polynomial degrees, all circuits, or an arithmetic lower bound.

## 3. Results

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|258|3861|43|
|260|3455|43|
|261|3409|43|
|262|2291|44|
|263|1523|44|
|264|1477|44|
|265|1112|44|
|266|1066|44|
|267|742|44|
|268|712|44|
|269|608|44|

There is no259 row because258 already has a smaller degree bound.
The fixed43-witness frontier additionally includes262/2380 and264/1810,
then ends at266/1344. The fixed45-witness frontier ends at272/608. Complete
lists and concrete group assignments are in the receipt.

The four improvements use SOS with maximum ordinary residual degree206.
At265 the group weights are556,555; at266 they are532,533; at267 they
are371,371,369; at268 they are353,356,356. The265 and267 bases normalize
the geometry strong equation and use its positive-scale projection.
The266 and268 bases normalize neither strong equation and use the same
geometry projection. The polynomial ledgers are respectively134M+131A,
133M+133A,134M+133A and133M+135A.

For the first three displayed partitions, the SOS average-weight lower
bound is attained. A two-group anchor has degree at least the total
weight plus the smallest factor weight, which is4 in these bases;
this exceeds1112 and1066. A three-group anchor has degree at least
the total weight, which exceeds742. Thus none improves those SOS values. The268
optimum additionally depends on the actual discrete factor weights.
Their total is1065, so a three-group maximum355 would force every group
to have weight355. One factor weighs252. The other large weights are
304,185,152 and101; all the smaller factors together weigh71. To complete
the252 group to355 requires103: none of304,185,152 fits;101 leaves2,
smaller than any remaining positive weight; and all small weights alone
give at most71. Thus355 is impossible, and the displayed maximum356 is
optimal. This gives a short certificate independent of the optimizer.
The new plans move old factors between groups, instead of only placing
the lower-history factor into previously selected partitions.

## 4. Reproduction and review scope

```sh
python3 neary_woods_universal_offset_partitions.py
```

Author receipt generation and a separate fresh replay recompute sixteen
searches,480 emitted ledgers and44 selected full schedules across both
program-bound interfaces. The108 complete-source contexts check1,728
affine output identities,432 on signed arbitrary assignments,864 direct
scalar finalizers and864 positive parent-to-new projections. There are217
height-gap cases whose algebraic parent gap is0. Both finalizers are
tested even when only one is optimal. The inherited independent Bell
enumeration checks21 small weighted problems through15,882 partition and
anchor choices, including cases with no ordinary residual.

These finite checks audit literal sources and the optimizer. They do not
replace the unbounded native/loader proofs or materialize full universal
Pell witnesses. Different partitions need not agree away from their zero
sets; the arbitrary-point identity here always compares the **same**
partition before and after the affine offset change.

Author writer and fresh default replay pass. An independent full proof,
source and subset-recurrence review, with a separate fresh replay, passes
after clarifying the two-group anchor lower bound. Its own executor and
manual affine map checked512 complete output identities,128 signed, across
64 contexts covering every base, both bound interfaces and both finalizers;
256 separately assembled scalar finalizers,64 zero-height lifts and64
output closures also passed. An independent subset enumeration found19
weight355 subsets in the268 base and verified that all171 pairs overlap,
confirming the impossibility of a three-group maximum355. The reviewer also
checked the short weight252 certificate and all four displayed within-base
optima. All five local links resolve. No source change was needed in review.
