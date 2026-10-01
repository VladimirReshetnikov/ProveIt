# Repartitioning the recovered initial bound improves six degree points

> The [native-bound successor](neary_woods_universal_native_bound254.md)
> changes eight base degree dictionaries and reaches254/1203 and262/392/43w.
> This packet's exact finite frontier applies to its original bound source;
> the new degree dictionaries have not yet been exhaustively repartitioned.

The [literal compiler](neary_woods_universal_initial_bound_partitions.py)
reruns the complete finite partition search after the
[254-operation initial-bound rewrite](neary_woods_universal_initial_bound254.md).
It improves six points of that packet's mapped frontier without increasing
operation counts. For example, the258-operation bound falls from858 to854,
and the263-operation bound from306 to302. The minimum-cost point remains
**254=133M+121A**,43 witnesses, degree at most1379; the low-degree endpoint
remains **266=133M+133A**,44 witnesses, degree at most212.

All sixteen inherited native bases and every disjoint factor partition,
with either allowed finalizer, are covered. The objective optimizes guarded
propagated degree bounds, not exact polynomial degrees or arbitrary
arithmetic circuits. The [receipt](neary_woods_universal_initial_bound_partitions.json)
contains every best-by-group-count ledger and the selected full sources.
The complete U9, ordinary input, four positive program parameters and
shifted E'=E-1 recipe are unchanged. The separate fifth bound interface is
also checked. The established75/87 bounds remain separate.

## 1. Regrouping preserves complete positive zeros within a base

The254 source supplies the positive height D directly. Its canonical
positive-zero theorem first restores native typing and the history radix,
using only D>=1 and the actual large fixed multiplier. The typed initial
residue and the valid input's bounded zero runs then force its initial
integer below D. Chronological transport and the sentinel argument restore
the positive lower sign. In particular the old height gap D-W is at least2.
The parent theorem therefore restores every individual unit factor to+1,
and every remaining ordinary residual is zero, on a valid program/input
slice.

For a partition into nonempty group products G_j, use either

    sum_i r_i^2 + sum_j(G_j-1)^2,

or choose one anchor a and use

    G_a*(1+sum_i r_i^2+sum_(j!=a)(G_j-1)^2)-1.          (1)

Either integer equation forces every group product to1 and every ordinary
residual to0. For the anchored form, the parenthesized positive integer
has integer product1 with G_a, so both are1. Multiplication of the group
products restores the canonical single product. The complete254 theorem
then forces each individual factor to1, so every other regrouping holds.
Conversely those individual conditions satisfy every partition and both
finalizers.

Thus regrouping preserves the full positive zero set within each fixed
native base on valid shifted program/input slices. Across different
strong/scale treatments use the inherited canonical extensions and
projections; there is no claim of equality of supplied-coordinate tuples
between bases. Every base retains the complete ordinary-input universal
relation.

## 2. Actual sources and their triangular identities

There are sixteen bases: independently retain or normalize each native
strong equation, and independently retain or project each native positive
scale coordinate. Their witness counts are45 minus the number of projected
scale coordinates. A source guard requires the complete canonical254 base.
The compiler reconstructs the same chosen partition and anchor through the
active257,256 and255 ancestry before applying the guarded254 height change.
This keeps every active parent map aligned with the emitted finalizer.

It separately removes the canonical product gates from the new254 source
and directly emits the requested products/finalizer. Both literal schedules
must agree. Source closure, all comparisons, domains, group products and
counts are checked. This validation charges the actual fixed-numeral
multiplications and every finalization gate.

For every partition, the exact arbitrary-integer identity to its aligned
255 parent is still

    eta_parent=D-W, D=W+eta_parent.

W is the unchanged literal loader expression and does not depend on the
height coordinate. Every retained register, residual and factor agrees
under this triangular polynomial map, hence so does the complete grouped
output. The map is not affine in all inputs, and its inverse may be
nonpositive off zero. At a new positive zero on a valid slice the254
language proof gives eta_parent>=2. Thus regrouping does not weaken its
positive-zero bijection or silently invoke a signed parent theorem.

## 3. Exact finite optimization objective

Let c count the closure of the individual factors and ordinary comparisons,
n the factor count, m the ordinary comparison count, and g the number of
groups. Both standard finalizers cost

    c+n+3m-1+2g,

except m=0,g=1 with an anchor, which emits just the product minus1 and costs
c+n. Every reported ledger is checked on the complete emitted source.

Let w_i be the propagated degree bound of factor i, r the largest ordinary
residual bound, and d_j the sum of weights in group j. The objective is

    SOS:       2 max(r,d_0,...,d_(g-1));
    anchor a:  d_a+2 max(r, all d_j with j!=a).          (2)

The [existing exact subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.py)
is rerun with the actual254 weights. For the unanchored groups its
recurrence enumerates every first group containing the least remaining
factor index and minimizes the maximum of that group's weight and the
recursive complement optimum. Every anchor subset is then tried alongside
the SOS choice. Lower-bound pruning uses only largest-factor and average
bounds; greedy partitions supply upper bounds, not completeness assumptions.
The [previous full partition proof](neary_woods_universal_history_scale_partitions.md)
provides the recurrence and cost justification, including the one-group
special case. No restriction to the previously selected partitions remains.

The new height has degree1 rather than3. In the default base the three
history upper/global/lower weights change from4,4,4 to2,2,3. All other
weights are unchanged, but a partition's objective need not decrease by a
uniform amount. Every plan is compiled and its complete propagated degree
is compared with(2). Only the inherited guarded exact main-norm cancellation
is used; no zero-equation substitution lowers a degree estimate.

## 4. The optimized finite frontier

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|254|1379|43|
|256|1237|43|
|257|1191|43|
|258|854|43|
|259|601|44|
|260|555|44|
|261|454|44|
|262|408|44|
|263|302|44|
|264|272|44|
|265|228|44|
|266|212|44|

Compared with the mapped254 schedules, the degree improvements are
858→854 at258 operations;458→454 at261;412→408 at262;306→302 at263;
274→272 at264; and230→228 at265. The original254 note retains its correct
historical mapped-family claims.

With43 witnesses fixed, the frontier additionally contains259/808,
260/610 and262/456; the259 point improves the mapped bound814. With45
witnesses fixed, the complete list is

    261/848,262/590,263/548,264/442,265/400,
    266/296,267/268,268/222,269/212.

The receipt also stores the44-witness-only frontier, starting at258/859,
and every group assignment and native treatment for all strata.

Some explicit optimal group weights make the improvements transparent.
At258, the two SOS weights are427,426; at261 they are227,226; at262 they
are203,204. At263 the weights151,151,151 attain the average-weight bound.
At264 they are135,136,136; at265 they are112,113,114,114. The266 endpoint
uses106,100,100,101 and ordinary residual bound74. All these examples use
SOS; cheaper frontier points may use an unsquared anchor.

The minimum propagated bound212 has a short certificate over the whole
finite family. Put Wmax=max_i(w_i), Wmin=min_i(w_i). SOS has bound at least
2 max(r,Wmax). If a largest factor belongs to the anchor, its bound is at
least Wmax+2r; otherwise it is at least Wmin+2 max(r,Wmax). The minimum of
these three expressions is at least212 in every base. The distinct pairs
(Wmax,r) remain

    (106,74),(228,192),(246,62),(490,14),(490,2),(490,0).

The displayed266 SOS attains212. This certifies a floor for the stated
propagated objective only; it is not a lower bound on exact degrees or on
other universal polynomial circuits.

## 5. Reproduction and validation

```sh
python3 neary_woods_universal_initial_bound_partitions.py
```

The checker reruns sixteen searches and480 literal ledgers across both
program-bound interfaces. Fifty selected full sources cover the combined
and witness-specific frontiers. There are114 complete-source contexts,
including both finalizers on every base even when not selected by the
optimizer:912 direct scalar/group checks and912 complete triangular
parent identities, with456 signed assignments and685 nonpositive
algebraic inverse gaps. These are arbitrary-point identities, not full
native Pell fixtures. Every source closure and the212 floor is checked.
The independent Bell enumerator also compares21 small weighted problems
through15,882 partition/anchor choices with the reused dynamic program.

A separate author scratch executor manually evaluated the loader expression
and height map for all twelve distinct improved schedules across both bound
interfaces. It passed192 complete grouped output identities,96 signed,
including group values and direct scalar finalizers. The scratch search also
checked all480 literal ledgers before this packet was written. Author
receipt generation and a separate fresh replay pass; all five local links
and whitespace checks pass.

Root independently checked24 weighted exact-search instances with one to
eight factors by enumerating15,885 Bell partitions and79,323 anchor
objectives. A separate sorted-prefix-anchor calculation independently
derived the unlimited-group floor in all sixteen actual bases: the family
floor is212, and the fixed43-witness floor is456. Root then independently
reviewed the complete final proof and source, including the aligned
ancestral maps, canonical guards, cost special case, grouping equivalence
and finite optimization scope, and passed a fresh default replay of all480
ledgers and114 contexts without findings.

Franklin independently reviewed the full proof, source and ancestry and
passed a fresh replay without findings. His separate executor/manual maps
checked528 complete parent/register/group/finalizer identities (264 signed)
across88 contexts, covering all sixteen bases, both interfaces and both
finalizers, with388 nonpositive formal parent gaps. Independent propagation
checked88 degree/closure/domain/cost contexts,240 best-group objectives,
four frontier extractions and sixteen floor certificates. A separate
literal closure pricing check matched all480 multiplication/addition
ledgers. Five local links and whitespace checks pass.

The trio is frozen after the author and both independent reviews. No
frozen parent, shared navigation or Git state was changed by this packet.
