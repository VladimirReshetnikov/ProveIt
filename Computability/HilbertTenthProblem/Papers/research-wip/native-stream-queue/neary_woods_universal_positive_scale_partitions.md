# Positive scales and grouped units:301 operations with degree at most608

The [positive-scale291 construction](neary_woods_universal_positive_scale291.md)
and [coupled factor grouping](neary_woods_universal_joint_and_coupled_partitions.md)
combine into a new finite family of complete ordinary-input U9 polynomials.
Its lowest displayed degree bound is **608**, achieved with
**301=142M+159A** polynomial operations, **257=127M+130A** certificate
operations, **15 comparisons** and **50 positive existential coordinates**.
The minimum operation count remains291 with49 witnesses and degree at
most3980.

The [source](neary_woods_universal_positive_scale_partitions.py) and
[receipt](neary_woods_universal_positive_scale_partitions.json) give the
literal schedules. The frontier below has two objectives: operation
count and propagated degree bound. Witness counts vary; it is **not**
a three-objective Pareto claim involving witness count. A separate
49-witness frontier preserves useful alternatives that the two-objective
comparison discards.

Every schedule retains the same fixed U9 program, four positive program
parameters and ordinary positive input. The independent fifth-duration-
bound interface is also retained. Grouping preserves the accepted outer
relation, rather than every supplied positive zero of the coupled parent.
No exact degree, unrestricted optimality or change to the separate75/87
route is claimed.

## 1. Sixteen bases with a complete positive interpretation

Keep both native cores indexed and coupled. Independently choose the
strong treatment in each core, giving four choices. Independently apply
the positive-scale rewrite in either core, giving another four choices.
All sixteen bases are built from the frozen source modules; no parent
circuit or receipt is edited.

For a selected core, the scale rewrite replaces

    X=q*w, r+beta=X

by

    bound=r+b, X=q*bound.

It reuses both arithmetic gates, removes one comparison and one supplied
coordinate, and saves3 final-polynomial operations. The positive forward
map is

    w_old=r+b, beta_old=q*(r+b)-r.

The reviewed inverse b=w_old-r is positive at every coupled zero,
including its negative joint-index branch, because the raw exponential
and population equations give w_old>r. Both native scales and indices
are independent of all changed coordinates, as checked transitively by
the inherited rewrite. The maps preserve every unit factor and all other
residual values. Their proof applies unchanged to either independent
strong-normalization choice.

Each grouped zero forces all original outer residuals zero and the total
unit product1. The coupled theorem therefore gives the complete accepted
outer relation, after undoing the positive-scale coordinate changes.
For completeness, each accepted outer instance has the earlier indexed
parent's all-factor-1 witnesses. Any chosen strong normalizations use
their independent five-auxiliary reconstructions. Coupling gives both
linear factors1, and the positive-scale inverse preserves every factor
value. These witnesses satisfy every partition.

This argument does not require all coupled-parent zeros to have every
factor1: the coupled joint index and checksum may still be negative
together. The positive-scale change itself is a positive-zero bijection;
the subsequent grouping is only an equivalence of accepted outer instances.

## 2. Literal counts and the unchanged exact partition optimizer

Write t for the number of normalized strong equations, b for the number
of positive-scale changes, and g for the number of nonempty factor groups.
Here 0<=t,b<=2. Before grouping, there are11+t factors and
13-t-b ordinary outer comparisons. Removing the old product and building
the g group products gives the exact ledgers

    certificate operations =259+2t-g,
    comparisons =13-t-b+g,
    positive witnesses =51-b,
    polynomial operations =297-t-3b+2g,
    polynomial M=142+t-b,
    polynomial A=155-2t-2b+2g.                       (1)

The certificate additions/subtractions remain130. The source's closure
audit charges every factor and group multiplication, checks each binary
operation, and verifies that every emitted gate reaches the output.

For factor groups with propagated degree bounds d1,...,dg and largest
ordinary-residual bound r, the two finalizers are

    sum residual^2 + sum (group_product-1)^2,
    anchor*(1+sum residual^2+sum other_group_residual^2)-1.

Their bounds are respectively

    2*max(r,d1,...,dg),
    d_anchor+2*max(r,other group bounds).             (2)

Their literal costs are identical. The second factor of the unsquared
form is an integer at least1, so a zero makes it and the anchor both1;
no sign assumption on the anchor is used away from zeros.

The source directly calls the frozen exact subset dynamic program from
the coupled partition packet. For each subset S and group count k, that
program minimizes the maximum group sum by enumerating the group
containing the least element of S. It then enumerates every possible
unsquared anchor subset. Greedy partitions provide upper bounds only;
all pruning uses proven lower bounds. No change is made to this optimizer
or to the literal grouping compiler.

Applying it to every base and every group count is exhaustive for(2) in
this finite family. This does not optimize actual expanded degrees or
consider other factor formulas, fewer coupled/indexed cores, arbitrary
arithmetic rewrites or other Diophantine constructions.

## 3. The two-objective frontier

The nondominated operation/degree-bound pairs are:

| Polynomial | M | A | Degree bound | Witnesses | Normalized | Positive scales | Groups | Certificate | Comparisons |
|---|---:|---:|---:|---:|---|---|---:|---:|---:|
|291|142|149|3980|49|Both|Both|1|262|10|
|292|141|151|3486|49|Geometry|Both|1|260|11|
|293|140|153|3440|49|Neither|Both|1|258|12|
|294|143|151|2322|50|Both|Geometry|1|262|11|
|295|142|153|1554|50|Geometry|Geometry|1|260|12|
|296|141|155|1508|50|Neither|Geometry|1|258|13|
|297|142|155|1142|50|Geometry|Geometry|2|259|13|
|298|141|157|1098|50|Neither|Geometry|2|257|14|
|299|142|157|766|50|Geometry|Geometry|3|258|14|
|300|141|159|734|50|Neither|Geometry|3|256|15|
|**301**|**142**|**159**|**608**|**50**|Geometry|Geometry|4|**257**|**15**|

The one-group rows use the unsquared finalizer; the remaining rows use
SOS. Counts and bounds include all program coordinates and agree on
both program-duration interfaces. The only algebraic degree cancellation
used is the inherited main-norm identity, whose literal source premises
are checked before applying it.

The default301 schedule has group bounds304,280,282,276 and ordinary
residual bound206. Thus its15-comparison SOS has degree at most608.
Its certificate costs257=127M+130A, and SOS adds15M+29A, giving
301=142M+159A. Compared with the earlier304/608 schedule, it removes
one positive coordinate and one comparison by changing only the geometry
scale.

The value608 is also a lower bound on the **propagated objective** in
this family. With the joint strong equation unnormalized, its auxiliary
factor has bound at least304 and the outer residual bound is at least206.
An SOS therefore has bound at least608; an unsquared anchor containing
that factor has bound at least304+2*206=716, while an anchor omitting it
has bound greater than608. With the joint strong norm normalized, the
auxiliary factor bound is at least708 and the residual bound at least44.
An SOS has bound at least1416; an anchor containing that factor has bound
at least708+2*44=796, and an anchor omitting it does worse. All sixteen
actual source cases satisfy these premises. This is not a lower bound
on actual polynomial degree outside this conservative objective.

## 4. Alternatives retaining49 witnesses

Restricting to two positive-scale changes keeps49 witnesses throughout.
The complete restricted cost/degree-bound frontier is

    291/3980,292/3486,293/3440,294/2380,296/1810,298/1344.

The last three points are not on the unrestricted cost/degree frontier:
that frontier offers lower degree bounds at the same costs using50
witnesses. They remain useful when49 witnesses is a separate constraint.

| Polynomial | M | A | Degree bound | Certificate | Comparisons |
|---|---:|---:|---:|---:|---:|
|294|141|153|2380|259|12|
|296|141|155|1810|258|13|
|298|141|157|1344|257|14|

These three schedules normalize geometry only and use SOS with two,
three and four groups respectively. The298 schedule has group bounds
620,672,484,570 and ordinary residual bound570. All six restricted
frontier schedules are emitted and checked on both program interfaces.

The API `build(operations=301)` selects the default two-objective point;
`build(operations=298,witnesses=49)` selects the restricted1344-bound
alternative. This explicit witness-count argument avoids confusing the
two different298-operation schedules.

## 5. Exact source audits and their limits

There are192 optimal group-count schedules across the sixteen bases,
with384 literal ledgers over both program interfaces. The receipt emits
the22 unrestricted frontier/interface sources and all12 fixed49 sources.
Six of the latter reuse exactly the same audited schedules already on
the unrestricted frontier; the other six receive additional audits.

The complete grouped-output checks total3,840, including1,920 signed
assignments. They cover all emitted schedules and32 off-frontier
singleton partitions across all bases and interfaces. The off-frontier
cases alternate SOS and unsquared finalizers. A separate192 complete
scale-lift identities,96 signed, check the positive coordinate maps
across all twelve nonempty scale/normalization choices on both interfaces.
These include96 strictly positive forward lifts and coordinate round trips.

Fixed numerals use consistent finite substitutions for these exact
integer identities; the actual fixed U9 recipes remain unchanged. No
finite sample is asserted to materialize a full positive native Pell
zero. The positive-domain proof supplies the accepted-input equivalence,
and the inherited exact recurrence proves the finite search scope.

```sh
python3 neary_woods_universal_positive_scale_partitions.py
```

The final author writer and fresh default replay pass. All four local
links resolve, and all192 optimal schedules have identical ledgers and
degree bounds on both program interfaces. An independent reviewer read
the full proof/source and ran the refreshed default replay; all passed
without findings. A separate literal executor checked256 complete grouped
outputs,128 signed,192 manually constructed scale lifts and32 dependency
closures. That review also checked all384 ledger and degree-envelope
formulas, the canonical positive inverse, grouping scope and608 objective
floor.
The root reviewer independently completed the final source/proof review
and a fresh default replay with no findings.
