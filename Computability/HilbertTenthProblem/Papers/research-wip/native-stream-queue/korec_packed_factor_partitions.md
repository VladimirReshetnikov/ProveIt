# Counter factor partitions trade380/21549 for391/3896

The [literal compiler](korec_packed_factor_partitions.py) expands the
[selector-sharing380 construction](korec_packed_selector_sharing380.md)
into four complete native bases and optimizes every disjoint factor
partition and SOS or anchored finalizer in each base. The minimum remains
**380=141M+239A**,50 positive witnesses and degree at most21549. Keeping
50 witnesses gives **388=141M+247A**, degree at most7704. One extra witness
allows **391=142M+249A**, degree at most3896.

These are actual strongly universal U21 counter sources with one fixed
positive program parameter and ordinary positive input. The inherited
two-program interface has corresponding endpoints379/40706,387/14552
and390/7352. Its second fixed parameter is a dyadic C>=4 exceeding the
program index; it is not an additional ordinary input. The
[receipt](korec_packed_factor_partitions.json) keeps the two interfaces
separate. The independent75/87 and U9 results are unchanged.

The degree numbers are guarded propagated upper bounds. This packet proves
an exact optimum of a specified finite source family, not exact polynomial
degrees or lower bounds on unrestricted arithmetic circuits. Within one
fixed base, every grouping has the same supplied positive zeros on valid
program/input slices. Across different bases the accepted outer relation
is preserved through coordinate maps and fresh strong auxiliaries.

## 1. Four complete bases and their positive equivalence

Start with the complete `units` form of selector380. Its parent proof in
[zero-range397](korec_packed_zero_range397.md) recovers the positive native
fields before dyadic typing, using the narrowed global range mask. None
of that outer source changes here. In particular its computed padded
ports give the paid identities

    S=5+Bp+q*(Bp+q*Zp), r=(q-1)*S, q>=16, S>0.       (1)

The two independent choices are whether to normalize the strong equation
and whether to project the native scale coordinate. All outer units remain.

For the projected scale retain the source definition

    X=q*(S+beta), beta>0.

For the ordinary scale introduce one positive witness w, replace that
definition by X=q*w, and retain the comparison

    X=r+beta, beta>0.                                (2)

Both give q|X and X>r before any native sign, rank or bit theorem. In the
projected case X-r=S+q*beta>0 by(1). Every positive projected tuple maps to
the ordinary graph by

    w=S+beta_projected,
    beta_ordinary=q*w-r=S+q*beta_projected.           (3)

This preserves every old coordinate except the positive gap, and makes
the added comparison identically true. It is an all-integer graph map;
the two complete polynomials need not agree away from zeros. Conversely,
at an ordinary zero the complete native theorem gives X=2^(2r+1), with
q<r. Consequently X>q*r and w=X/q>r>S. Thus
beta_projected=w-S is a positive integer. This proves the scale-coordinate
bijection on positive zeros without imposing w>S before soundness.

For strong normalization write A=a+2, Delta=A^2-1 and t=i*c^2. The
normalized source has the unit factor and auxiliary coefficient

    Ns=f^2-Delta*t^2, K_normalized=Delta^2*t^2.

The ordinary source deletes Ns from the factor list, computes

    K_ordinary=Delta*(f^2-1),

and retains the full comparison (i*c^2)^2=K_ordinary. It drops the now
unused normalized Q multiplication. This is the full strong equation,
including the square-divisibility requirement; no rank premise is weakened.

The local sign/rank proof in
[native coupled units, Sections1--2](native_binary_index_coupled_units.md)
explicitly treats both strong forms. For the ordinary auxiliary norm its
coefficient is0 or1 modulo4; the normalized coefficient is a square.
Both exclude the negative norm sign before rank recovery. The proof uses
X>r, q|X and both strict ratios, which hold in both scale bases above.
The unchanged positive fields, raw population argument and r=1 modulo16
then exclude the negative native index. The outer counter proof types
the time radix and history scale, recovers one-hot selection, the selected
range/zero mask, transport signs and the actual accepting chronology.
All individual native and outer factors are+1 at any positive zero on a
valid slice, for each of the four bases.

There is also a direct strong extension check. A normalized zero maps to
an ordinary zero by i_ordinary=Delta*i_normalized. Conversely the full
native theorem gives c=psi_A(J), J=2r+1=3 modulo4. The canonical construction
in [native norm units, Section3](native_binary_norm_units.md) rebuilds only
f,i,j,o,y, starting with m=2cJ. It makes the normalized strong factor and
the auxiliary norm+1 and preserves the auxiliary linear equation. Those
five private coordinates do not enter q,S,r,X,a,c, either strict ratio,
the first/main norm, or any counter/control/port source. Their replacement
therefore preserves every outer comparison and unit. This is existential
extension equivalence, not a bijection of all supplied strong tuples.

Combining the two independent arguments proves that all four bases accept
exactly the same ordinary inputs for each valid fixed program. Every
construction retains the complete paid loader and unbounded history.

## 2. Literal rewrites and arbitrary-point checks

`base(normalized,scaled,program_radix)` constructs a complete canonical
source, with one group and its product-minus-one or anchored finalizer.
Here `scaled=True` means the projected formula X=q*(S+beta). The ordinary
source adds `counter_partition_w`; it has51 witnesses instead of50.
The strong change reinstates the actual comparison
`native__ic22=native__R16`, and the ordinary scale reinstates its actual
bound comparison. Source closure removes the obsolete normalized Q and
old unit-product chains. Every remaining charged row reaches the output.
Historical parent dictionaries retain their old meaning; active flags,
removed-comparison metadata and positive-scale contract describe this base.

`regroup(original,partition,anchor)` requires equality to one complete
canonical packet, including its domains and interfaces. A partition must
contain every individual factor exactly once, in nonempty disjoint groups.
This guard excludes modified callers, hidden gap exports and incomplete
sources. Regrouping changes only products and the final comparisons.

For an independent arbitrary-integer oracle, apply(3) and, in an ordinary
strong base, set i_ordinary=Delta*i_normalized. Let V=of-c and let N3 denote
the auxiliary norm. Exact polynomial identities then give

    ordinary_strong_residual=Delta*(1-Ns),
    N3_ordinary=N3_normalized+Delta*(Ns-1)*(V^2-y^2).  (4)

The added ordinary-scale residual is identically zero under(3). Every
other individual factor is unchanged. The checker verifies every retained
source register outside the six explicitly altered strong definitions
and the altered bound definition, as well as(4) and all residuals. These
identities use no Pell equation or division by a factor. Positive forward
maps and signed off-zero assignments are both checked. They substantiate
the implementation; positive-zero equivalence uses Section1.

## 3. Complete finite partition objective

Let u_i be the individual factors, r_i the retained ordinary residuals,
and G_j the product over group j. The available complete finalizers are

    SOS = sum_i r_i^2 + sum_j(G_j-1)^2,

    anchor a = G_a*(1+sum_i r_i^2
                         +sum_(j!=a)(G_j-1)^2)-1.    (5)

At an integer zero, either finalizer forces every ordinary residual to
zero and every group product to1. In the anchored case its second factor
is a positive integer; hence both factors are1. The product of all groups
is the canonical base product. Section1 then forces every individual u_i
to+1 at positive zeros on valid slices. Thus every other partition and
anchor vanishes on exactly that supplied tuple. This proves equality of
positive zero sets within a fixed base, not merely projection equivalence.

Let c be the number of gates in the individual-factor/residual closure,
n the number of factors, m the number of ordinary comparisons and g the
number of groups. Literal final-source cost is

    c+n+3m-1+2g,                                    (6)

except that m=0,g=1 with an anchor costs c+n: it emits just the factor
product minus one. Each chosen plan is compiled and its actual opcode
count is checked against(6).

Let w_i be the propagated degree bounds of the factors, let r be the
maximum ordinary residual bound (zero when absent), and let d_j be the
sum of the w_i in group j. The objective is

    SOS:      2*max(r,d_0,...,d_(g-1)),
    anchor a: d_a+2*max(r,all d_j with j!=a).          (7)

The [reviewed subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.md)
considers every nonempty anchor subset and the all-SOS alternative at
every group count. It partitions the remaining indices by considering
every first group containing the least remaining index, then recursing
on the complement. Lower bounds only prune impossible improvements;
greedy schedules supply upper bounds. Thus the search is exact for this
finite objective. All group-count winners are emitted and their actual
source degrees must equal(7). The only algebraic reduction in degree
propagation is the inherited guarded main-norm polynomial cancellation;
no relation holding merely at zeros is substituted into a degree bound.

## 4. Frontiers and attained finite degree floors

The one-program unrestricted frontier is:

| Operations | M | A | Degree upper bound | Positive witnesses |
|---:|---:|---:|---:|---:|
|380|141|239|21549|50|
|382|141|241|18951|50|
|384|141|243|13456|50|
|385|142|243|9114|51|
|387|142|245|6512|51|
|389|142|247|4542|51|
|391|142|249|3896|51|

With50 witnesses fixed, the complete list is

    380/21549,382/18951,384/13456,386/10254,388/7704.

With51 witnesses fixed, it is

    384/14256,385/9114,387/6512,389/4542,391/3896.

The two-program unrestricted list is

    379/40706,381/35804,383/25424,384/17199,
    386/12300,388/8574,390/7352.

Its fixed50 list ends with385/19374 and387/14552 after the first three
unrestricted rows. Its fixed51 list is
383/26917,384/17199,386/12300,388/8574,390/7352.

For a compact lower certificate put Wmax=max_i(w_i), Wmin=min_i(w_i).
Every SOS objective is at least2*max(r,Wmax). If a largest factor is in
the anchor, the anchored objective is at least Wmax+2r; otherwise it is
at least Wmin+2*max(r,Wmax). Their minimum bounds every partition/anchor.
The four base certificates are:

| Strong | Scale | One-program floor | Two-program floor | Witnesses |
|---|---|---:|---:|---:|
|ordinary|ordinary|3896|7352|51|
|ordinary|projected|7704|14552|50|
|normalized|ordinary|7096|13400|51|
|normalized|projected|8352|15776|50|

The one-program391 source attains3896 with four SOS groups of weights
1622,1948,1623,1317 and ordinary residual maximum1302. The388 source
attains the fixed50 floor7704. The two-program endpoints attain the
corresponding floors. The checker explicitly compares each combined and
witness-specific endpoint with the minimum certificate for its eligible
bases. These are exact finite propagated minima, not global lower bounds.

## 5. Reproducible evidence

Run `python3 korec_packed_factor_partitions.py`; `--write` regenerates the
receipt. It records all eight base/interface searches,68 emitted group-count
winners, six full frontiers and their attained floors, and20 selected complete sources with their
parameters, auxiliaries, opcode ledger and hash.

The source checks192 complete base factor/residual maps, including96
signed assignments and96 positive forward coordinate maps. Separate
manual products and finalizers check288 complete grouped outputs,
including144 signed assignments, over selected frontier sources and
additional three-group SOS/anchored schedules in every base. Six malformed
callers or partitions are rejected. The independent small Bell enumeration
checks24 weighted instances and15885 partitions, including their anchor choices, against
the optimizer. These are algebraic/component checks, not materialized
full native Pell zeros. Author receipt generation, root fresh replay and
two independent full proof/source/dependency reviews with fresh replays
pass without remaining findings. Active identity metadata was corrected
to distinguish the selector380 parent from regrouping within a fixed base.

Each independent reviewer exhaustively enumerates101148 Bell partitions
across all eight bases, including447340 anchors and101148 SOS choices,
and reproduces every group-count optimum and all six frontiers. One checks
68 opcode/degree/closure ledgers,544 manually finalized outputs (272 signed)
and256 independent base correction maps (128 signed and128 positive lifts).
The other checks72 additional grouping contexts and576 manual cross-base
and grouped outputs (288 signed). Final metadata and all six attained-floor
certificates pass; all seven local links and whitespace checks pass.
