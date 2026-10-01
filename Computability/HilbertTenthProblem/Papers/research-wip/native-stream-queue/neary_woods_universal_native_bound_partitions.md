# Exact repartitioning after the native bound reaches258/742

The [literal partition compiler](neary_woods_universal_native_bound_partitions.py)
reoptimizes the complete sixteen-base family after the
[paid native bound rewrite](neary_woods_universal_native_bound254.md).
It improves the258-operation degree bound from756 to **742** and, with43
witnesses fixed, the259-operation bound from712 to **696**. The minimum-cost
point remains **254=133M+121A**,43 positive witnesses, degree at most1203.
The family reaches **262=133M+129A**,43 witnesses, degree at most392, and
**266=133M+133A**,44 witnesses, degree at most212.

All degree claims are bounds propagated through actual emitted sources,
with the inherited guarded main-norm cancellation. The optimization is
exhaustive over the stated finite family of factor partitions and finalizers;
it does not establish exact polynomial degrees or global circuit optimality.
The [receipt](neary_woods_universal_native_bound_partitions.json) contains all
best-by-group-count ledgers, witness strata and selected complete sources.
The complete U9 program/input convention, four positive program parameters
and ordinary positive input are unchanged. The separate fifth duration-bound
interface is also checked. The established75/87 bounds remain separate.

## 1. The sixteen bases and their positive-zero scope

Choose independently whether to normalize each of the geometry and joint
native strong equations, and whether to project each positive-scale
coordinate. This gives the same sixteen bases as the
[initial-bound partition family](neary_woods_universal_initial_bound_partitions.md).
There are45 minus the number of projected scales positive witnesses.

Exactly eight bases have the joint positive-scale projection. In those
bases the new native definition is

    S=A+1+(q+1)(B+(q-1)Z), r=(q-1)S,
    X=q(S+beta).

The native-bound theorem proves a positive-zero bijection to its former
definition X=q(r+beta_old), on valid shifted program/input slices. The exact
coordinate map is beta_old=beta+S-r. Positivity in the reverse direction
uses the recovered X=2^(2r+1); it is not assumed before typing.

The other eight bases retain their ordinary joint-scale comparison and
their original source. The new bound is not silently applied to an
ineligible core. Thus this packet searches sixteen specified graphs,
not an unlisted larger family of coordinate changes.

For any one canonical base, its complete positive-zero theorem forces all
individual native, mask and history factors to+1, and every remaining
ordinary residual to0, on valid slices. For the rewritten bases this also
follows by the exact factor-preserving positive coordinate map to the
initial254 parent. Write G_j for disjoint nonempty products of the factors.
The available finalizers are

    sum_i r_i^2 + sum_j(G_j-1)^2,

or, with one chosen anchor a,

    G_a*(1+sum_i r_i^2+sum_(j!=a)(G_j-1)^2)-1.        (1)

At an integer zero, either form gives all G_j=1 and all r_i=0. For the
anchored form the parenthesized integer is positive, so its integer
product with G_a can equal1 only when both equal1. Multiplying all groups
then gives the canonical product equation. Its soundness theorem forces
every individual factor to+1, hence every other partition and anchor also
vanishes. The converse is immediate from those individual conditions.

Therefore all regroupings of one fixed base have exactly the same supplied
positive zero set on valid program/input slices. Across distinct bases the
inherited positive extensions preserve the accepted outer relation; no
tuple identity across different strong/scale treatments is claimed.

## 2. Literal grouping and aligned coordinate maps

`base(normalized,scaled,merge_bound)` constructs the chosen canonical graph.
`regroup(original,partition,anchor)` requires that complete canonical
packet. It first reconstructs the chosen grouping throughout the existing
initial254 ancestry. It then applies the guarded native bound only in the
eight eligible bases. Thus every stored parent uses the same grouping and
anchor as the current source.

An independent compilation path groups the already changed canonical
source directly. The two paths must have identical complete emitted rows,
outputs, comparisons, factor/group metadata, parameter and witness lists,
and operation counts. Source closure is checked, including all fixed
numeral multiplications and every finalization gate.

On arbitrary integer assignments, a single explicit composite map reaches
the aligned255 parent. Write D for the supplied history height and W for
the literal loaded initial word minus one. The map is

    eta_parent=D-W,
    beta_parent=beta+S-r       in the eight rewritten bases,

with beta unchanged in the other eight. W is independent of the history
height and the native bound witness; r and S are independent of that native
witness. To invert, first recover D=W+eta_parent and then reverse the bound
substitution. All retained source registers, factors, groups and the entire
output agree. These are triangular polynomial identities, not affine maps
in all supplied coordinates. Formal inverse gaps may be nonpositive away
from zeros. At valid positive zeros the two reviewed parent proofs establish
their positivity in the required order.

## 3. Complete finite optimization

Let c be the number of gates in the closure of the individual factors and
ordinary comparisons, n the factor count, m the ordinary comparison count,
and g the number of groups. The exact final-source cost is

    c+n+3m-1+2g,

except for m=0,g=1 with an anchor, when the product-minus-one source costs
c+n. This exception is priced from its actual single final subtraction.
Every plan's multiplication/addition ledger is checked against its literal
emitted output, rather than inferred from the objective alone.

Let w_i be the guarded propagated degree of factor i, r the largest retained
ordinary residual degree, and d_j the sum of weights in group j. The exact
objective being optimized is

    SOS:      2 max(r,d_0,...,d_(g-1));
    anchor a: d_a+2 max(r, all d_j with j!=a).          (2)

The [reviewed subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.md)
is rerun on every actual base's changed weight list. For unanchored groups,
the recurrence considers every first group containing the least remaining
factor index, and minimizes the maximum of its weight and the optimum on
the complement. It then considers every possible anchor subset and the
SOS alternative. Largest-factor and average lower bounds justify its
pruning; greedy schedules supply only upper bounds. Thus every disjoint
partition and every anchor is represented for every group count.

The S rewrite leaves operation counts fixed, but it changes six joint
factor weights and, in some bases, an ordinary strong residual weight.
Consequently the old selected schedules do not prove this new optimum.
Each new plan is emitted in full and its propagated degree is checked
against(2). No zero equation or canonical Pell value is used for a degree
reduction. The parent polynomial sources remain unchanged.

## 4. Frontiers and finite-family floors

The unrestricted frontier is:

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|254|1203|43|
|256|1061|43|
|257|1015|43|
|258|742|43|
|259|601|44|
|260|514|43|
|261|454|44|
|262|392|43|
|263|302|44|
|264|272|44|
|265|228|44|
|266|212|44|

At258 the optimal two SOS groups have weights371 and370, with ordinary
residual bound160. They improve the mapped S-bound degree756 to742.
At259 with43 witnesses fixed, the two SOS weights347 and348 improve712
to696. The full fixed43 frontier is

    254/1203,256/1061,257/1015,258/742,
    259/696,260/514,262/392.

Its262 endpoint uses four SOS groups with weights196,181,182,182 and
ordinary residual bound160. Both it and the258 example normalize only the
geometry strong equation and project both scales. The259/696 example
retains both ordinary strong equations and projects both scales.

The44-witness frontier is unchanged by the new search:

    258/859,259/601,260/555,261/454,262/408,
    263/302,264/272,265/228,266/212.

With45 witnesses fixed, the unchanged list is

    261/848,262/590,263/548,264/442,265/400,
    266/296,267/268,268/222,269/212.

These last two strata are still fully included in the search; their
unchanged optimum is a result, not an omission of eligible alternatives.
The266/212 source uses no normalized strong equations, projects only the
geometry scale, and has SOS group weights106,100,100,101 with residual
bound74. This base correctly retains its ordinary joint scale.

There are short certificates for both endpoint floors. Put
Wmax=max_i(w_i) and Wmin=min_i(w_i). SOS has objective at least
2max(r,Wmax). If a largest factor belongs to the anchor, its objective is
at least Wmax+2r; otherwise it is at least Wmin+2max(r,Wmax). The minimum
of these three expressions is at least212 in all sixteen bases. The
distinct pairs (Wmax,r) are

    (106,74),(196,160),(246,62),
    (426,14),(426,2),(426,0).

The266 SOS attains212. With43 witnesses fixed, the four corresponding
certified lower bounds are392,392,454,426, and the262 SOS attains392.
Thus212 and392 are exact minima of the respective finite propagated
objectives. They are not lower bounds on exact polynomial degree or on
other universal arithmetic circuits.

## 5. Reproducible checks

Run `python3 neary_woods_universal_native_bound_partitions.py`; `--write`
regenerates the receipt. The checker reruns sixteen searches and480 literal
ledgers across both bound interfaces. Fifty selected complete sources
cover the unrestricted and all witness-specific frontiers. Additional
four-group SOS and anchored schedules exercise every base independently
of the selected optimum, for114 complete-source contexts in total.

Those contexts give912 direct scalar/group/finalizer checks and912 complete
composed parent/register/output identities, with456 signed assignments.
The formal maps include698 nonpositive height-parent gaps and293 nonpositive
native-parent gaps among368 native-gap lifts. These are recorded rather
than silently treated as positive witnesses. The independent Bell enumerator
also compares21 small weighted instances through15,882 partition/anchor
choices with the reused dynamic program. Four incompatible canonical
callers are rejected. These finite algebraic and component checks are not
claims to have materialized complete large native Pell zeros.

Author receipt generation and a separate fresh default replay pass. All five
local links and whitespace checks pass. Independent proof/source review and
a fresh replay pass without findings. A separate source executor checks128
manually composed complete register/output maps across all sixteen bases,
both interfaces, and three-group SOS and nonzero-anchor schedules. Half use
signed coordinates;98 inverse height gaps are nonpositive off zero. Its
independent scalar finalizer calculation agrees in every case.
