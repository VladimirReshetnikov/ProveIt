# Exact selector reuse shifts the counter frontier to378/21549--389/3896

> The [repunit-factored family](korec_packed_repunit_partitions.md) transports
> every plan here through a further two-operation saving, with the same
> degree dictionary. Its one-program frontier starts376/21549 and reaches
> 384/7704 at50 witnesses or387/3896 at51 witnesses.

The [complete successor family](korec_packed_selector_reuse_partitions.py)
applies the [two-addition selector rewrite](korec_packed_selector_sharing378.md)
to every source in the [four-base partition family](korec_packed_factor_partitions.md).
Every corresponding complete polynomial is identical on all supplied integer
coordinates, and every degree dictionary is unchanged. Each source costs
exactly two fewer additions. Thus the one-program route now starts at
**378=141M+237A**,50 positive witnesses and degree at most21549, reaches
**386=141M+245A** at degree at most7704 with50 witnesses, or
**389=142M+247A** at degree at most3896 with51 witnesses.

The fixed two-program interface has the analogous endpoints377/40706,
385/14552 and388/7352. The [receipt](korec_packed_selector_reuse_partitions.json)
records both interfaces separately, all68 group-count winners, six frontiers,
their attained degree floors and20 selected complete sources. These are
complete strongly universal U21 sources; the separate75/87 and U9 frontiers
are unchanged. The degree bounds are propagated upper bounds, with exact
optimization only inside the inherited finite family.

## 1. The same local identity in every complete base

The parent has four strong/scale bases per fixed program interface. It
retains either the normalized or ordinary full strong equation, and either
projects the native X scale or retains its extra positive witness. These
changes leave every selector and control definition untouched.

Write E_i=edge_i_hat-1. The two new graph identities are

    D5_111=(E_4+E_16)+E_18
          =E_4+coefficient_tail_198,
    coefficient_tail_198=E_18+E_16,

    linear_sum_166=(linear_sum_164+E_14)+E_28
                  =D4_109+linear_sum_164,
    D4_109=E_14+E_28.                                (1)

The pair registers in the right sides are already paid. Delete only the
private prefixes D5_110 and linear_sum_165. Associativity and commutativity
prove both identities on arbitrary integers. Each reused pair depends
only on selector leaves; topological sorting introduces no cyclic control
or native dependency. The selector378 source guards every literal definition,
every private-prefix consumer and the absence of erased public exports.

The new `base(normalized,scaled,program_radix)` first constructs the complete
canonical parent base, then invokes that guarded row helper. It takes the
individual-factor/ordinary-residual closure and rebuilds the canonical
single-group finalizer. `regroup` requires equality to this complete new
base before changing any partition or anchor. A caller cannot use the local
helper alone as evidence of universality for an arbitrary source.

Induction through the sorted arithmetic graph gives equality of every
retained register, every ordinary residual and every individual factor.
Partition products and either complete finalizer therefore agree exactly
with their corresponding parent polynomials. Parameters, witnesses,
comparisons and public interfaces are unchanged. In particular this layer
has the identity map as its positive-zero bijection to each corresponding
parent source, even for an ordinary-strong or ordinary-scale base.

This identity is distinct from the parent's cross-base theorem. Different
strong bases still require fresh canonical private auxiliaries, and different
scale bases use the positive scale-coordinate maps. Within a fixed base,
all partitions have the same supplied positive zeros on valid slices by
the parent's sign theorem. All of these meanings are retained unchanged.

## 2. Why all finite optima shift by exactly two

The two deleted prefixes have degree one in the selector hats, and both
replacements in(1) have the same propagated degree as the old sums. Thus
every individual-factor weight and every ordinary-residual degree is
unchanged. The checker compares complete degree dictionaries for every
emitted winner, including the guarded main-norm cancellation.

Let c,n,m,g be the parent's individual-factor closure size, number of
factors, ordinary comparisons and partition groups. The new closure has
c-2 gates; n,m,g are unchanged. Every plan therefore loses two gates in
the formula c+n+3m-1+2g, and also in its single-anchor/no-residual special
case c+n. Literal opcode comparisons require the same number of
multiplications and exactly two fewer additions in both certificate and
polynomial ledgers. Full closure checks exclude newly unused charged rows.

The parent search considers every partition and available finalizer in
each of the four bases. Its objective depends only on the unchanged factor
weights and ordinary-residual maximum. Therefore it returns exactly the
same degree optimum at each group count. Since the cost shift is uniform
over all plans and bases, the entire unrestricted and witness-specific
frontiers translate by minus two operations. Repeating an optimizer on
different weights is unnecessary: there are no different weights here.
The checker nevertheless emits and checks all68 parent winners and
independently aggregates every frontier from those new source ledgers.

The floor certificates are likewise unchanged. Taking their minimum over
the eligible bases and checking equality at the new endpoints establishes
the same attained finite propagated minima:7704 with50 witnesses and3896
overall for one program;14552 and7352 for two. No exact-degree or general
arithmetic-circuit lower bound is claimed.

## 3. Complete frontiers

The one-program unrestricted frontier is:

| Operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|378|21549|50|
|380|18951|50|
|382|13456|50|
|383|9114|51|
|385|6512|51|
|387|4542|51|
|389|3896|51|

With50 witnesses fixed it is

    378/21549,380/18951,382/13456,384/10254,386/7704.

With51 witnesses fixed it is

    382/14256,383/9114,385/6512,387/4542,389/3896.

For the two-program interface the unrestricted list is

    377/40706,379/35804,381/25424,382/17199,
    384/12300,386/8574,388/7352.

The fixed50 list replaces the last four rows by383/19374 and385/14552.
The fixed51 list is381/26917,382/17199,384/12300,386/8574,388/7352.
These programs retain their respective one- or two-parameter conventions;
no program coordinate is counted as the ordinary input or as a witness.

## 4. Reproducible source checks

Run `python3 korec_packed_selector_reuse_partitions.py`; `--write` regenerates
the receipt. The all-plan identity is a symbolic proof. Supplementary
checks compare every retained register and complete output on288 arbitrary
integer assignments,144 signed, across selected frontier sources and
three-group SOS/anchored schedules in all eight base/interface contexts.
Another288 manual group/finalizer calculations include144 signed cases.
The inherited strong/scale correction formulas are checked on192 complete
base maps, including96 positive forward lifts and96 signed assignments.
Four malformed or preceding canonical callers are rejected.

The stored source hashes, exact ledgers, full closures, identical degree
dictionaries and attained-floor certificates make the constant shift
reproducible. These checks do not materialize full native Pell zeros.
Author receipt generation, root fresh replay, and independent full
proof/source/dependency review with a further fresh replay pass without
findings. A separate executor checks72 degree/opcode/closure/domain
contexts and576 complete register/restored-prefix/output identities,
288 signed, including72 assignments with all selectors zero. It also
verifies all68 winner transfers and all six complete frontiers.

A second source/proof audit checks the exact changed source dictionaries
in all eight bases, retained domains and active metadata, every retained
naive register degree, all68 guarded degree/opcode/closure ledgers and
the six frontier transfers. All four local links and whitespace checks
pass. Both reviews distinguish this exact same-coordinate rewrite from
the inherited existential equivalence between different strong bases.
