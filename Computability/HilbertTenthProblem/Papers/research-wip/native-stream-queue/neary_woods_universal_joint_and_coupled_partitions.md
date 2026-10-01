# Grouped coupled units: a304-operation polynomial of degree at most608

The complete [coupled297 U9 compiler](neary_woods_universal_joint_and_coupled.md)
admits useful operation/degree tradeoffs. In particular, a single
**304=143M+161A** polynomial has total degree **at most608**, with the
same **51 positive existential coordinates**, four positive program
parameters and ordinary positive input. Its certificate costs
**257=127M+130A**, with **16 comparisons**. The297-operation minimum
in this family retains the earlier degree bound2311.

The [source](neary_woods_universal_joint_and_coupled_partitions.py) and
[receipt](neary_woods_universal_joint_and_coupled_partitions.json) compile
every displayed schedule. An exact subset dynamic program finds the
best propagated degree bound at each cost within a specified finite
family: both cores remain indexed and coupled, either strong equation
may be normalized, all unit factors are partitioned into disjoint groups,
and at most one group is used as an unsquared outer multiplier.

Each schedule preserves the complete accepted outer relation. It need
not preserve every positive supplied tuple of the coupled parent: that
parent can leave the joint index and checksum simultaneously negative.
No exact-degree, unrestricted circuit-optimality or new75/87 claim is
made. The fixed U9 program and its paid ordinary-input interface remain
unchanged.

## 1. Four complete bases and the sign distinction

Start with the positive-root joint-AND compiler and apply both native
index units and both coupled linear units. Independently choose whether
to normalize the strong equation of the geometry core and the joint
core. The [two-core unit construction](neary_woods_universal_joint_and_units.md)
already proves that these strong normalizations preserve the accepted
outer relation: soundness embeds the normalized coordinate by
`i_old=Delta*i`, and completeness rebuilds each core's five canonical
auxiliaries independently. Its consumer audit proves that these rebuilds
do not change the outer input, program, recoder or history coordinates.
Thus the mixed normalization choices require no new completeness promise.

Write N0,N1,N3 for the first, main and auxiliary norm factors, Nk for
the index unit, Nl for the coupled linear unit, and C for the sole joint
checksum. A normalized core also has its strong norm Ns. The ordinary
strong equation remains an outer comparison when that core is not
normalized. The guarded degree bounds on the actual factor expressions
are as follows; subscripts g and j denote geometry and joint cores.

| Factor | Geometry | Joint |
|---|---:|---:|
| N0 |8|152|
| N1 |12|252|
| N3, ordinary strong |16|304|
| N3, normalized strong |36|708|
| Ns, when present |22|406|
| Nk |5|185|
| Nl |5|101|
| C, present only in the joint core |—|49|

Consequently the four bases have:

| Normalized cores | Factors n | Sum of factor bounds | Largest outer-residual bound r | Original polynomial cost |
|---|---:|---:|---:|---:|
| Neither |11|1089|206|299|
| Geometry only |12|1131|206|298|
| Joint only |12|1899|185|298|
| Both |13|1941|185|297|

These are bounds on the literal polynomials, including all program
coordinates. The only algebraic cancellation used is the inherited,
source-guarded main-norm identity. No zero-set equation lowers a degree.

Let the retained outer residuals be r1,...,rm and the listed integer
factors be f1,...,fn. The coupled parent output is

    (product_i fi)*(1+sum_j rj²)−1.                   (1)

At its positive zeros the coupled theorem restores the complete outer
relation. Its proof forces both linear signs and the geometry index
sign positive. The joint index and checksum may both be−1; that branch
restores the earlier parent with the strictly positive changes
F0_old=F0−2 and beta_old=beta+2. This is a conditional normalization,
not a theorem that every factor equals1 in the original coordinates.

On the other hand, every positive zero of the earlier indexed parent,
with the chosen strong treatment, has every norm, index and checksum
factor equal1. Its two linear comparisons give both Nl=1 as well.
These all-positive-factor witnesses remain available for every accepted
outer instance. This distinction supplies completeness for every grouping
below.

## 2. Safe grouped finalizers and their literal cost

Partition the factors into g nonempty disjoint groups and denote their
products by V1,...,Vg. The ordinary grouped polynomial is

    sum_j rj² + sum_i(Vi−1)².                         (2)

Alternatively choose one group a and use

    Va*(1+sum_j rj²+sum_(i!=a)(Vi−1)²)−1.             (3)

Both have exactly the same integer zero set, namely all rj=0 and
all Vi=1. For(3), its second factor is an integer at least1; their
product can equal1 only when both are1. No off-zero sign assumption
on Va is needed.

Every grouped zero is a coupled-parent zero, since product_i Vi=1
and all outer residuals vanish. Therefore it is sound for the parent's
complete outer relation. Conversely every accepted outer instance has
the earlier all-factor-1 witnesses from Section1, which satisfy every
grouping. This proves complete outer equivalence. It does not assert
that all coupled-parent witness tuples satisfy a chosen partition, nor
does it assert off-zero polynomial identity with(1).

The source reuses the exact dependency-closure and grouping compiler
from the [earlier partition packet](neary_woods_universal_joint_and_partitions.md).
Let b be the number of certificate gates in the closure of all factors
and retained outer comparisons. Removing the parent's final product
removes exactly n−1 multiplications; this equality is source-audited.
Building g disjoint products costs n−g multiplications. Thus the new
certificate has b+n−g gates and m+g comparisons. Either finalizer
costs exactly

    b+n+3m−1+2g.                                    (4)

Relative to the corresponding one-group coupled parent, the complete
polynomial adds exactly2(g−1) additions. Its multiplication count is
unchanged. No factor is duplicated or evaluated for free, and every
emitted gate reaches the final output. All51 supplied positive witnesses
and both the four-program and independent fifth-bound interfaces remain.

## 3. Degree planning and exact finite-family search

For a group I put d(I)=sum_(i in I) deg_bound(fi). Its product has
degree at most d(I). With r the bound on the retained outer residuals,
the propagated bounds for(2) and(3) are respectively

    2*max(r,d(I1),...,d(Ig)),
    d(Ia)+2*max(r,max_(i!=a)d(Ii)).                   (5)

The search optimizes precisely these bounds. It does not expand the
large integer polynomials or claim their actual degrees attain them.

For a set S of factor indices and an integer k, define

    F(S,k)=min over k nonempty groups partitioning S
                 of their maximum group weight.

The base cases are F(S,1)=d(S), F(S,|S|)=max_(i in S)d({i}), and
F(empty,0)=0. For the remaining cases choose the group T containing
the least index in S:

    F(S,k)=min_T max(d(T),F(S\T,k−1)),               (6)

where T contains that least index and |S\T|>=k−1. Every unordered
partition occurs in this recurrence, and no ordering of the other
groups affects the objective. Memoization over bitmasks avoids a full
Bell13 enumeration.

The implementation starts from a valid greedy partition solely to
obtain an upper bound. Its certified lower bound is the maximum of
the largest individual weight and ceil(d(S)/k). Equality certifies
optimality; otherwise it evaluates(6). A subset whose weight already
meets or exceeds the current best cannot yield a strict improvement
and may be skipped. These are exact bound tests, not heuristic stopping
conditions.

For the unsquared option, enumerate every possible nonempty anchor
subset T. The remaining groups have best possible maximum
F(S\T,g−1), so the second objective in(5) becomes

    d(T)+2*max(r,F(S\T,g−1)).                        (7)

The same valid lower bounds permit pruning a candidate anchor that
cannot improve the current answer. Thus the best value is found for
every group count, both finalizers and all four bases. This is an
exhaustive optimization within the stated family, not merely a list
of selected schedules. It does not cover changing the factor formulas,
uncoupling a core, changing the positivity theorem or arbitrary circuits.

## 4. The frontier and a literal304/608 schedule

The resulting nondominated operation/degree-bound pairs are:

| Polynomial | M | A | Degree upper bound | Normalized cores | Groups / finalizer | Certificate | Comparisons |
|---|---:|---:|---:|---|---|---:|---:|
|297|144|153|2311|Both|1 / unsquared|262|12|
|298|143|155|1543|Geometry|1 / unsquared|260|13|
|299|142|157|1501|Neither|1 / unsquared|258|14|
|300|143|157|1132|Geometry|2 / SOS|259|14|
|301|142|159|1092|Neither|2 / SOS|257|15|
|302|143|159|756|Geometry|3 / SOS|258|15|
|303|142|161|730|Neither|3 / SOS|256|16|
|**304**|**143**|**161**|**608**|Geometry|4 / SOS|**257**|**16**|

Every row has51 positive witnesses. The same counts and degree bounds
hold with an independent fifth program-duration bound. These are
successors of the coupled construction, not revisions of any frozen
historical source or receipt.

The default304 schedule normalizes only geometry and uses the four
products

    V1=N3_j,
    V2=N1_j*Ns_g,
    V3=N3_g*C*Nk_g*Nk_j,
    V4=N1_g*N0_g*N0_j*Nl_g*Nl_j.                     (8)

Their degree bounds are304,274,275,278. The twelve unchanged outer
residuals have degree at most206. Hence the16-comparison SOS has
degree at most2*304=608. Its certificate is257=127M+130A, and its
SOS adds16M+31A, giving304=143M+161A.

There is also a simple lower bound for the degree objective in this
family. When the joint core is not normalized, its N3 factor alone
has bound304 and the outer bound is206. Any SOS therefore has bound
at least608. An unsquared anchor containing that factor has bound at
least304+2*206=716; an anchor not containing it has bound greater
than608. When the joint core is normalized, N3 has bound708: an SOS
has bound at least1416, while an anchor containing it has bound at
least708+2*185=1078, and an anchor omitting it does worse. Thus608
is the smallest possible displayed degree bound in this family.
This is not a lower bound on the actual polynomial degree or on any
larger class of Diophantine constructions.

## 5. Source replay and limits of the evidence

The receipt records48 optimal schedules by base and group count,
with96 full literal ledgers across the two program interfaces. All16
frontier/interface schedules include their complete encoded polynomial
sources, witnesses, parameters and source hashes. The dependency audit
checks that every counted gate reaches the output and that every source
register has a unique definition.

There are1,024 independently assembled full grouped-output identities,
512 signed, using consistent finite replacements for each fixed numeral
role. They compare each factor and retained source register with the
actual coupled base and evaluate(2) or(3) directly. These are arbitrary
integer circuit identities, not a numerical claim to expand positive
Pell zeros or a comparison with the parent's off-zero polynomial.

An independent complete partition enumeration validates the subset DP
on24 weighted instances with one through eight factors, covering15,885
partitions and every anchor choice. The recurrence proof establishes
the exhaustive scope on the actual11–13 factors; the smaller tests
corroborate its implementation.

```sh
python3 neary_woods_universal_joint_and_coupled_partitions.py
```

Author receipt generation and fresh default replay pass. Root full
proof/source review and fresh default replay pass without findings,
including the actual304,274,275,278 group bounds and the608 objective
floor. A separate root executor checked256 complete-output identities,
128 signed, for32 schedules outside the displayed frontier across all
four normalization choices and both program interfaces. These retain
the arbitrary-integer algebraic scope above.

A second independent full proof/source review and fresh default replay
pass without findings. That reviewer used a separate Bell generator on
36 weighted cases through nine factors, checking105,768 partitions
against every DP objective. It also checked eight dependency closures
and192 arbitrary partition/anchor complete-output identities,96 signed,
with an independent executor across all bases and program interfaces.
The review confirms the accepted-outer scope, exact counts and the608
bound-objective floor; all five local links resolve.
