# Repunit factoring transports the four-base counter frontier

The [source](korec_packed_repunit_partitions.py) applies the exact
[repunit376 identity](korec_packed_repunit376.md) to every plan in the
[selector-reuse partition family](korec_packed_selector_reuse_partitions.md).
Each complete source loses **two total operations**, comprising **two more
multiplications and four fewer additions**, with an identical polynomial,
identical supplied coordinates, and identical complete propagated degree
dictionary relative to its corresponding parent plan.

The one-program frontier now starts at **376=143M+233A**, with50 positive
witnesses and degree at most21549, and reaches **387=144M+243A**, with51
witnesses and degree at most3896. The separate two-program frontier starts
at375 and reaches386 at degree7352. Both retain ordinary positive input.
The inherited restrictions on the fixed program parameters are unchanged.
No new compiler, sign or chronology theorem is needed.

## 1. Uniform identity across the finite family

The parent has four native bases: ordinary or normalized strong equations,
and an ordinary or projected native scale bound. Each has the same paid
counter radix powers and the same seven-addition repunit source. The
repunit helper replaces that source by

\[
 1+D+\cdots+D^7=(1+D)(1+D^2)(1+D^4),
\]

at cost3A+2M. Its literal power, private-consumer, export and fresh-name
guards pass on all eight canonical base/interface combinations. The five
erased repunit prefixes are private in every base, and the final repunit
and all later factors and ordinary residuals have their old values on
arbitrary integer assignments.

`base(normalized,scaled,program_radix)` constructs the exact canonical
parent, calls the guarded local row helper, and takes the factor/residual
closure of the new rows. `regroup` accepts only one of these complete
canonical bases. It then uses the parent's unchanged group products and
finalizer construction. The new rows remain live because every partition
uses every factor and retains every ordinary comparison.

Therefore, for **every** allowed partition and anchor, not only the
selected winners, the source has the same complete integer polynomial as
its corresponding parent. No supplied variable or positive-domain
constraint changes. Within one fixed base, the inherited regrouping
proof gives the same positive zeros on the valid program/input slices.
Across the different strong/scale bases, the inherited fresh auxiliary
extensions and scale-coordinate maps give the same accepted outer
relation; no equality of all supplied tuples across bases is claimed.

## 2. Exact transport of the finite objective

Let \(c\) be the number of gates in a base's factor/residual closure,
\(f\) its number of unit factors, \(m\) its ordinary comparisons, and
\(g\) the number of nonempty factor groups. The inherited literal price is

\[
 c+f+3m-1+2g,
\]

except for a single anchored group with no ordinary comparisons, whose
price is \(c+f\). The new factorization changes only \(c\), by exactly−2,
in both cases. Multiplication and addition counts change by+2 and−4.

All factor degrees and the maximum ordinary-residual degree are unchanged.
For an all-SOS finalizer the degree objective remains twice the largest
ordinary/group degree. For anchor \(j\), it remains that group's degree
plus twice the largest other-group or ordinary degree. Thus every objective
value is unchanged and every cost is shifted by−2. Ties, optimal group
counts, anchors, witness strata and the finite degree-floor certificates
transport directly from the exact parent search.

This is an exact optimum in the **inherited finite family**, with both
program interfaces considered separately. It is not a new search over
arbitrary arithmetic circuits, coordinate changes or compiler models.
The degree objective remains a guarded propagated upper bound, not the
exact degree of a fully expanded and simplified polynomial.

## 3. Complete frontiers and witness strata

The unrestricted one-program frontier is:

| Operations | M | A | Degree upper bound | Witnesses |
|---:|---:|---:|---:|---:|
|376|143|233|21549|50|
|378|143|235|18951|50|
|380|143|237|13456|50|
|381|144|237|9114|51|
|383|144|239|6512|51|
|385|144|241|4542|51|
|387|144|243|3896|51|

For the separate two-program interface:

| Operations | M | A | Degree upper bound | Witnesses |
|---:|---:|---:|---:|---:|
|375|144|231|40706|50|
|377|144|233|35804|50|
|379|144|235|25424|50|
|380|145|235|17199|51|
|382|145|237|12300|51|
|384|145|239|8574|51|
|386|145|241|7352|51|

With exactly50 witnesses, the one-program frontier instead continues
from380/13456 through382/10254 to384/7704. The two-program version
continues from379/25424 through381/19374 to383/14552. With exactly51
witnesses, the one-program frontier starts at380/14256 before joining
381/9114; the two-program frontier starts at379/26917 before joining
380/17199. All six complete frontier lists are stored in the receipt.

The finite attained degree floors are3896 overall and at51 witnesses,
and7704 at50 witnesses, for the one-program interface. They are7352 and
14552 respectively for the two-program interface. These are floors only
of the specified propagated family objective.

## 4. Source and receipt checks

The [receipt](korec_packed_repunit_partitions.json) stores all68 transported
best-by-group-count plans, the six frontiers and attained floor
certificates, and20 distinct complete selected source schedules with
hashes. It also prices all eight canonical bases and off-frontier
three-group SOS and anchored examples. Every complete ledger and degree
dictionary is compared with its exact parent counterpart.

Author receipt generation and a separate fresh default replay pass. Across44 base/group/anchor contexts,
352 whole retained-register, restored-prefix and complete-output identities
include176 signed assignments. Separately352 manual factor-group and
scalar-finalizer checks include176 signed assignments. The checker rejects
four malformed or preceding canonical bases. These are source and
component identities; they do not claim materialized full native Pell
solutions. The underlying across-base completeness theorem is inherited,
not inferred from the finite tests.

Run `python3 korec_packed_repunit_partitions.py`; `--write` regenerates the
receipt. `build(operations=None, program_radix=False, witnesses=None)`
chooses a frontier schedule, with witness filters50 or51 if requested.
The canonical `base`, `regroup`, `search`, and `frontier` APIs expose the
same finite family. Independent full proof/source/dependency review and
a separate fresh replay passed without findings. That review checked all
eight canonical base dictionaries, all68 selected plans and64 additional
ordered or off-frontier partitions:132 complete degree, opcode, liveness
and scope contexts. Its own528 whole retained-register, restored-prefix,
output and manual-finalizer checks include264 signed assignments. All six
exact frontier transfers and six attained-floor checks passed. A final
root source/proof review and fresh receipt replay also passed. These
checks preserve the distinction between identical same-parent polynomials
and existential equivalence across native bases.
