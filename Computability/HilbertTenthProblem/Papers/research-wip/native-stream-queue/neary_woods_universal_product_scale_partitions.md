# Exact product-scale partitions reach257/710 and261/372

The [literal compiler](neary_woods_universal_product_scale_partitions.py)
reoptimizes all sixteen strong/scale bases after the
[product-scale253 construction](neary_woods_universal_product_scale253.md).
The minimum-cost source is **253=132M+121A**, with43 positive witnesses
and degree at most1147. Fresh partitions improve the mapped degree bound
at257 operations from712 to **710**, and at258 operations from666 to
**664**. The43-witness endpoint is **261=132M+129A**, degree at most372;
the full family still reaches **266=133M+133A**,44 witnesses, degree at
most212.

The complete U9 compiler has the same four fixed positive program parameters
and ordinary positive input, with its separate fifth duration-bound interface
also checked. Every stated degree is a guarded propagated upper bound for
an emitted source. This is an exact finite partition/anchor optimization,
not an exact-degree result or a global arithmetic-circuit lower bound.
The [receipt](neary_woods_universal_product_scale_partitions.json) records
all group-count optima, both interfaces, witness strata and selected sources.
The independent75/87 bounds are unchanged.

## 1. Exactly sixteen bases and their equivalence

Start with the [native-bound partition family](neary_woods_universal_native_bound_partitions.md).
Each native strong equation, geometry or joint AND, may be ordinary or
normalized; each native scale coordinate may be retained or projected.
The four independent choices give sixteen bases and45 minus the number
of projected scales positive witnesses.

For exactly eight bases the joint scale is projected. Apply product253 to
those bases. With history radix b, computed history scale P and low padded
scale q0, their top ports and native scale become

    T=P^9,
    H=H0+2T, M=M0+T, Z=Z0, q=q0*b*T.

The paid factorization and bound remain

    S=A+1+(q+1)(B+(q-1)Z), r=(q-1)S,
    X=q(S+beta).

The other eight bases retain the preceding ordinary joint-scale graphs.
No product-scale theorem for those ineligible graphs is assumed.

Product253 proves its local sign order from positive computed fields and
X>r, before any outer dyadic assumption. The native scalar theorem first
forces q dyadic. Its literal positive-factor decomposition then types both
b and P; the Mersenne argument fixes the history repunit sign. The top
bits2 and1 have zero AND, so all original lower history lanes are restored.
The paid loader, language-derived initial bound, chronology, and transport
signs then recover the same valid compiled input. The proof also establishes
that all individual factors are+1 at every positive zero on a valid slice.
Its converse rebuilds positive private joint-native witnesses at the changed
scale, while retaining the outer and geometry coordinates.

This distinction matters. The preceding-scale and new-scale positive zero
sets on identical supplied joint-native tuples are not asserted equal.
Their accepted outer projections agree. Changing strong or scale treatments
also preserves the accepted relation through their respective positive
extensions, rather than by identifying all private coordinates.

Within one fixed new base, however, regrouping does preserve the entire
supplied positive zero set on valid program/input slices. Let r_i be its
ordinary residuals and let G_j be products over disjoint nonempty groups
covering every individual factor. The available finalizers are

    SOS = sum_i r_i^2 + sum_j(G_j-1)^2,

    anchored = G_a*(1+sum_i r_i^2+sum_(j!=a)(G_j-1)^2)-1.   (1)

At an integer zero either expression forces every r_i=0 and every G_j=1.
For the anchored form its second factor is a positive integer, so both
integer factors must equal1. Multiplying all group equations gives the
canonical product equation. The complete fixed-base theorem then forces
every individual factor to+1; every other partition and anchor consequently
vanishes. This proves the precise within-base equality used in the search.

## 2. Literal regrouping and changed-port replay

`base(normalized,scaled,merge_bound)` constructs the chosen canonical graph.
`regroup(original,partition,anchor)` requires equality to that complete
canonical packet, including source, domains and interfaces. It first
reconstructs the chosen partition through the native-bound ancestry. In
an eligible base it reconstructs the exact guarded254 caller, checking
that the preceding optimizer added only its two documented provenance
fields, then applies product253. This keeps every stored parent aligned
with the current partition and anchor.

A second compilation path groups the changed canonical graph directly.
Both paths must emit identical complete source rows and output registers,
comparisons, factor/group metadata, parameter and witness lists, and counts.
Literal source closure includes every charged numeral product and finalizer.
The product-scale private-row/consumer guard is inherited unchanged.

The new and old-scale polynomials generally differ on arbitrary assignments.
For the algebraic checker, evaluate the aligned preceding255 source with
these four explicit definition overrides in the eight eligible bases:

    top_mask=2P^9,
    joined_H=H0+2P^9,
    joined_M=M0+P^9,
    native_q=q0*b*P^9.                                (2)

Also apply the older manual coordinate maps

    eta_parent=D-W,
    beta_parent=beta+S-r,

where D is the supplied history height and W is the paid input word minus
one. In the eight ineligible bases only the height map is needed and no
port definition is overridden. Here r and S in the second map are computed
from the new ports. All retained registers, factors, groups and complete
outputs agree with the resulting oracle. The coordinate maps invert by
first recovering D and then reversing the native gap substitution.

For eligible bases this is a **changed-port replay**, not an identity to the
unchanged preceding polynomial or a positive coordinate bijection between
scales. For ineligible bases it is the inherited triangular parent identity.
Negative formal inverse gaps away from zeros are recorded explicitly.
The positive-zero extension claim rests on Section1 and the reviewed
product-scale theorem, not on these arbitrary-point substitutions.

## 3. Exact finite objective and exhaustive search

Let c be the number of gates in the individual-factor/ordinary-residual
closure, n the number of factors, m the number of ordinary comparisons,
and g the number of groups. Literal final-source cost is

    c+n+3m-1+2g,

except for m=0,g=1 with an anchor: that source is just the individual
factor product minus one and costs c+n. Every chosen plan is compiled and
its actual multiplication/addition counts checked against this formula.

Let w_i be the guarded propagated factor bounds, r the largest ordinary
residual bound, and d_j the sum of weights in group j. The objective is

    SOS:      2 max(r,d_0,...,d_(g-1));
    anchor a: d_a+2 max(r, all d_j with j!=a).          (3)

The [reviewed subset dynamic program](neary_woods_universal_joint_and_coupled_partitions.md)
is rerun on each actual changed list of weights. For the unanchored groups
it considers every first group containing the least remaining index, then
recurses on the complement. Every nonempty anchor subset and the all-SOS
alternative are considered at each possible group count. Largest-factor
and average bounds provide sound pruning; greedy candidates provide only
upper bounds. Thus every disjoint partition and every available finalizer
is represented in this finite objective.

Product253 saves one multiplication in eight bases and changes their native
factor and sometimes residual bounds. Mapping only the preceding selected
schedules therefore does not establish the new optimum. All new plans are
emitted, and their source-derived degrees must equal(3). Degree propagation
uses only the inherited guarded main-norm polynomial cancellation, never
an equation valid merely at zeros or a canonical Pell witness value.

## 4. Frontiers and floor certificates

The unrestricted frontier is:

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|253|1147|43|
|255|1013|43|
|256|967|43|
|257|710|43|
|258|664|43|
|259|488|43|
|261|372|43|
|263|302|44|
|264|272|44|
|265|228|44|
|266|212|44|

The first seven rows are exactly the fixed43-witness frontier. At257 the
new two SOS groups have weights354 and355, with ordinary residual bound152.
This improves the mapped712 to710. At258 the two SOS weights332 and331
improve the mapped666 to664. The257 source normalizes only the geometry
strong equation; the258 source retains both ordinary strong equations.
Both project the two scales. The261 endpoint uses four SOS groups with
weights186,174,174,175 and residual bound152, giving372.

The fixed44-witness frontier is

    257/1140,258/859,259/601,260/555,261/454,
    262/408,263/302,264/272,265/228,266/212.

The new257/1140 endpoint uses134M+123A. The other rows retain their preceding
bounds. With45 witnesses fixed, the unchanged list is

    261/848,262/590,263/548,264/442,265/400,
    266/296,267/268,268/222,269/212.

The266/212 source retains both ordinary strong equations and projects only
the geometry scale, so it correctly belongs to the eight unchanged bases.
Its four SOS group weights are106,100,100,101, with residual bound74.

For a short floor certificate put Wmax=max_i(w_i), Wmin=min_i(w_i).
Every SOS objective is at least2max(r,Wmax). If a largest factor is in the
anchor, the anchored objective is at least Wmax+2r; otherwise it is at
least Wmin+2max(r,Wmax). Their minimum is a lower bound for every partition
and anchor. Across all sixteen bases that certificate is at least212,
which the266 source attains. In the four43-witness bases the certificates
are372,372,432,404, and the261 source attains372. These are exact minima
of the respective finite propagated objectives, not exact-degree or
unrestricted circuit lower bounds.

## 5. Reproducible checks

Run `python3 neary_woods_universal_product_scale_partitions.py`; `--write`
regenerates the receipt. It reruns all sixteen searches and480 literal
best-group-count ledgers over the two duration interfaces. Fifty-two selected
complete sources cover the unrestricted and every witness-specific frontier.
Four-group SOS and anchored checks on every base add64 contexts, for116
complete-source contexts.

The checks include928 independently calculated scalar/group/finalizer
outputs and928 complete composed register/output replays, with464 signed
assignments. Of the replays,384 use the four changed ports and544 are
unchanged-port parent identities. The formal maps include713 nonpositive
height-parent gaps and299 nonpositive native-parent gaps among384 native
gap lifts. The independent small Bell enumeration checks21 weighted
instances and15,882 partition/anchor choices against the dynamic program.
Four incompatible canonical callers are rejected. The receipt also maps
the preceding selected schedules from every witness stratum, so the two
additional repartition improvements are distinguished from the underlying
one-multiplication scale change.

These finite algebraic and component checks do not assert materialized full
native Pell zeros. Author receipt generation and a separate fresh default
replay pass. All five local links and whitespace checks pass. Independent full
proof/source/dependency review and two further fresh replays pass without
findings. A separate executor checks384 complete ancestor replays,192 signed,
and384 manual scalar/group/finalizer calculations across64 independent
five-group contexts, all sixteen bases and both interfaces. Half are changed-port
replays and half inherited parent identities;143 formal native gaps are
nonpositive. Its64 literal opcode/closure/domain checks, four frontier
aggregations, sixteen floor certificates and two chosen-base average bounds
for257/710 and258/664 also pass.
