# Repartitioning the positive history scale gives degree bounds down to212

The [literal compiler](neary_woods_universal_history_scale_partitions.py)
optimizes every factor partition and either allowed finalizer after the
[257-operation history-scale rewrite](neary_woods_universal_history_scale257.md).
The resulting finite frontier begins at **257=133M+124A**,43 positive
witnesses and degree at most1384, and reaches **269=133M+136A**,44 positive
witnesses and degree at most212. At43 witnesses it reaches265/456.

This is the complete U9 universal construction with the same ordinary
input and four positive program parameters. The offset recipe remains
E'=E-1. A separate fifth duration-bound parameter is supported with the
same ledgers. The overall75-certificate/87-polynomial frontier is unchanged.
The [receipt](neary_woods_universal_history_scale_partitions.json) includes
every best-by-group-count ledger and selected full literal sources.

## 1. Why the smaller scale degree survives every grouping

In the parent258 source the history scale was P=(b-1)J+1. The257 rewrite
instead computes P as the sum of the two supplied histories, three supplied
product hats and the positive global slack. It retains the integer factor

    N_P=P-(b-1)J.

Thus P has degree1 in the actual polynomial source rather than degree4:
the parent history height contains the degree3 loaded input, and J has
degree1. The joint native scale bound correspondingly falls from49 to16.
The parent proof establishes all pretyping native-field bounds even with
N_P=-1, restores native dyadic scales independently of this sign, and
excludes the negative repunit by its reserved top AND lane and a Mersenne
congruence. Only then does it decode the history. Every individual factor
equals1 on a complete positive zero on a valid program/input slice.

For every partition of the factors into nonempty group products G_j, use

    sum_i r_i^2 + sum_j(G_j-1)^2,                       (1)

or an anchored finalizer

    G_a*(1+sum_i r_i^2+sum_(j!=a)(G_j-1)^2)-1.          (2)

As integer equations, either forces all group products1 and all ordinary
residuals0. For(2), the parenthesized integer is positive and its product
with G_a is1, so both are1. Multiplying the group products recovers the
canonical single product. Its complete sign theorem then forces every
individual factor1. Conversely those individual conditions satisfy every
regrouping. This gives identical positive zero sets within each fixed base
on valid program/input slices. Across the sixteen native bases, keep the
inherited projections and canonical extensions, not a tuple bijection.

The source first applies the guarded257 rewrite to a canonical258 base,
then discards the old product gates and emits each new partition. The
active258 parent is also regrouped to the same partition and finalizer.
On the algebraic locus N_P=1, the substitution

    global_slack_parent=global_slack_new-1             (3)

makes the old and new scales, individual factors, residuals and complete
polynomials agree. This is a **conditional** polynomial identity. There
is no arbitrary-point identity between the old and new polynomials.
At genuine positive zeros the257 theorem proves the new slack at least17,
so(3) is positive; conversely every valid positive258 zero lifts by adding1
to that slack. This positive-zero equivalence therefore survives each
regrouping. The actual offset parameter is unchanged by(3).

## 2. Exact finite objective and literal source checks

There are sixteen bases: independently choose strong normalization and
positive-scale projection for each of the two native cores. Let c count
the closure of individual factors and ordinary comparisons, n the factors,
m the ordinary comparisons and g the groups. The complete polynomial costs

    c+n+3m-1+2g,                                     (4)

except for m=0,g=1 with an anchor, which emits just the product minus1 and
costs c+n. The257 closure saves one addition for every matching partition
of the258 parent. Every reported cost is checked on the actual emitted
source, including nonunit fixed-numeral multiplications and finalization.

Let w_i be the guarded degree bound on factor i, r the maximum ordinary
residual bound and d_j the sum of factor weights in group j. Optimize

    SOS:       2 max(r,d_0,...,d_(g-1));
    anchor a:  d_a+2 max(r, all d_j with j!=a).        (5)

The [exact subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.py)
is rerun with the new weights. It enumerates every first group containing
the least remaining index, recursively solves the complement, and tries
every anchor subset as well as SOS. Its pruning uses only valid largest-
weight and average-weight lower bounds; greedy schedules are upper bounds.
The [preceding partition proof](neary_woods_universal_offset_partitions.md)
establishes this recurrence and the exceptional cost case. Every new plan
is separately compiled and degree propagation is checked against(5).

Only the inherited guarded main-norm cancellation is used in propagating
degrees. Replacing the source definition of P legitimately reduces its
degree on arbitrary assignments; no relation holding only at zeros is
substituted into a polynomial to lower its reported degree. The objective
is a conservative bound, not the exact degree. All program coordinates
are included. Witness-specific frontiers are retained.

## 3. The complete operation/degree frontier

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|257|1384|43|
|259|1242|43|
|260|1196|43|
|261|858|43|
|262|606|44|
|263|560|44|
|264|458|44|
|265|412|44|
|266|306|44|
|267|276|44|
|268|230|44|
|269|212|44|

The fixed43-witness frontier additionally gives262/814,263/610 and265/456.
The fixed45-witness frontier ends at272/212. All tables and group assignments
are in the receipt. A slash separates operation count and degree bound.

At261, the two group weights429,429 attain the average-weight SOS bound.
At264 they are229,229; at266 they are152,153,153; at268 they are115,115,115,113.
These last three bases normalize only the geometry strong equation and use
only its positive-scale projection. At269, neither strong equation is
normalized and only the geometry scale is projected; the four group weights
are106,100,102,104, with maximum residual bound74. Hence(5) gives212.

The endpoint212 has a simple lower-bound certificate over the whole finite
family. Let W=max_i w_i. SOS has bound at least2 max(r,W). If the largest
factor is in an anchor, that finalizer has bound at least W+2r; otherwise
it has bound at least min_i(w_i)+2 max(r,W). The minimum of these three
lower bounds is at least212 in every base. The distinct pairs(W,r) are

    (106,74), (228,192), (246,62),
    (490,14), (490,2), (490,0).

The first pair gives the smallest bound212, attained by the displayed269
SOS. This certifies the minimum **propagated bound** in the stated family,
independently of the dynamic program. It is not a lower bound on the exact
degree of those polynomials or of arbitrary universal equations.

## 4. Reproduction and finite evidence

```sh
python3 neary_woods_universal_history_scale_partitions.py
```

The writer and fresh replay recompute sixteen searches and480 emitted
ledgers across both bound interfaces, with50 selected complete schedules.
There are114 complete-source contexts:912 direct scalar finalizers and912
conditional complete parent identities, with456 signed assignments.
The fixtures deliberately include247 nonpositive algebraic parent slacks;
these audit conditional identities only, not positive zeros. Both finalizers
are exercised across all sixteen bases regardless of the optimizer's choice.
The separate Bell enumerator checks21 small weighted problems through15,882
partition/anchor choices, including zero ordinary residuals.

These checks supplement the unbounded parent proof and audit source closures,
counts and the finite optimizer. They do not materialize enormous native
Pell witness tuples, claim arbitrary-point equality between different
partitions, or establish a global minimum arithmetic complexity.

Author writer and fresh default replay pass. An independent full proof,
literal-source and reused-optimizer review, with another fresh replay,
passes after correcting the prose description of the parent scale's
degree to4. Its own executor checked256 direct scalar outputs and256
complete conditional parent/register identities across64 contexts: all
sixteen bases, both bound interfaces and both finalizers, including128
signed assignments and52 nonpositive algebraic parents. It separately
checked64 output closures, independence of the defining repunit right
side from beta, all six(W,r) pairs, the degree-floor certificate, the
269/212 endpoint and the fixed43-witness endpoint265/456. All five local
links and whitespace checks pass. No arithmetic source change was needed.
