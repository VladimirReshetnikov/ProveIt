# Two fewer multiplications throughout the four-base factor family

The [source](tseytin_cross_offset_factor_partitions.py) and
[receipt](tseytin_cross_offset_factor_partitions.json) transfer the complete
[four-base factor family](tseytin_global_unit_factor_partitions.md) through
the exact [opposite-coordinate offset identity](tseytin_cross_offsets383.md).
Every matching partition and finalizer computes the identical integer
polynomial on the identical supplied coordinates, with two fewer
multiplications and no change in additions or propagated degree.

The combined operation / propagated-degree frontier is:

|Operations|M|A|Certificate gates|Comparisons|Degree bound|Strong / global treatment|
|---|---:|---:|---:|---:|---:|---|
|383|176|207|372|4|4714|normalized / unit|
|384|175|209|370|5|4134|ordinary / unit|
|385|175|210|368|6|4132|ordinary / equality|
|386|175|211|369|6|2900|ordinary / unit|
|388|175|213|368|7|2210|ordinary / unit|
|390|175|215|367|8|1664|ordinary / unit|

All rows retain62 positive witnesses, one fixed positive program parameter
A and ordinary positive input x. They use the actual24-tile C2 system,
the complete exponent52 relation and paid query loader. The valid program
recipe is unchanged: the digits of a,b,c,d,e,# are0,3,1,2,4,5 and the copy
tiles are ordered #,e,b,d,c,a. The universal ordinary-input representation
therefore transfers directly from each selected parent.

The finite optimum concerns these four specified factor bases, their
disjoint partitions and their SOS/anchor finalizers, using the stated
propagated bounds. It is not an exact expanded-degree claim or an optimum
over other arithmetic circuits. The separate75-certificate/87-polynomial
record is unchanged.

## 1. Guard the complete host before the local rewrite

The bases independently choose normalized or ordinary word strong
treatment, and the global unit G or its retained equality. They are
precisely the four bases of the preceding family. In particular the
ordinary treatment keeps its full strong comparison; no norm, inequality,
loader or chronological condition is weakened here.

`rewrite_base` first requires equality with the complete canonical prior
base. `rewrite` similarly calls the prior complete grouped-packet guard,
including its base choices, factor partition and anchor. Complete-source,
degree-bound and ledger APIs require the corresponding complete canonical
successor. Every factor, comparison, interface, program recipe, parameter,
witness and active partition export is retained.

The local helper receives all non-source metadata recursively as active
exports. It checks the literal paid selector sums, every affected row,
the exact consumers of each changed or deleted private value and the
absence of any private-value export. Thus applying the local identity
to a different factor grouping cannot expose an altered subtotal. Only
the old `source` and `factor_source` bodies are excluded from this export
test; both are replaced by their complete new guarded graphs.

The preceding base contract already reconstructs and checks the current
118 native/exponent rows and161 pretyping ancestors, the computed fields
and checksum, and the private five-coordinate strong dependency closure.
The present whole-parent guard composes with that contract rather than
accepting its stored metadata alone. It then proves every unchanged
factor and comparison from the actual local boundary identity. The final
source is sorted, all operands are checked, and every emitted row reaches
the complete polynomial output.

## 2. Exact identity for every grouping

Write h_i=Shat_i. The paid selector sums are

    U=h14+h16, V=h15+h17,
    CU=U+h21+h23, CV=V+h20+h22.

The common offset contains12(h14+h15)+20(h16+h17). Changing its two
coefficients to267 and275 adds255(U+V) without adding a gate. Replace
the two coordinate-specific portions by

    255U−3h14+512h20+1024h22
      = −767V−3h14+512(CV+h22)+255(U+V),
    255V−3h15+512h21+1024h23
      = −767U−3h15+512(CU+h23)+255(U+V).              (1)

These are polynomial identities over all integers. On each side three
multiplications and two additions become two multiplications and two
additions. The two common coefficient multiplications remain charged.
Consequently the combined affine ports `linear_constant__411` and
`linear_constant__430` remain identical, while the complete source loses
exactly2M. Private common offsets and coordinate subtotals need not agree.

The exact consumer/export guard confines those private differences to
the two unchanged boundary ports. Every factor, ordinary residual and
group product therefore has its old value. For group products U_j and
ordinary residuals R_i, both complete finalizers retain their values:

    SOS = sum_i R_i² + sum_j (U_j−1)²,
    anchor a = U_a*(1+sum_i R_i²+sum_{j!=a}(U_j−1)²)−1. (2)

This proves exact whole-polynomial equality with the matching prior plan
over arbitrary signed integer tuples, without assuming any equation,
valid program, positivity, one-hot selection or native typing. The
identity map thus gives a full positive-zero bijection for each matching
old/new plan, even outside the valid program slices.

This statement does not identify different plans or bases off their zero
sets. The preceding family's separate semantic scopes still apply: within
a fixed base, all groupings have the same supplied positive zeros on
valid program slices, because its individual-factor sign theorem makes
every factor+1. Between global treatments, the global slack shifts by1
and has a positive inverse on those slices. Between strong treatments,
five private auxiliary coordinates may be rebuilt; only accepted-input
equivalence is asserted in that direction. The global-unit sign mechanism
is the previously credited joint-bound mechanism transferred to this C2
source, not a new sign principle in this packet.

## 3. Complete finite objective transport

The new literal factor cores have the following costs. Here c is their
gate count, n the factor count, m the retained ordinary-comparison count
and g the number of nonempty groups.

|Strong|Global|c|n|m|Complete polynomial cost|
|---|---|---:|---:|---:|---:|
|normalized|unit|360|13|3|381+2g|
|normalized|equality|359|12|4|382+2g|
|ordinary|unit|359|12|4|382+2g|
|ordinary|equality|358|11|5|383+2g|

Both finalizers cost c+n+3m−1+2g. Indeed the products use n−g
multiplications; SOS spends three gates per ordinary or group residual
and combines the squares. An anchor omits one group residual but pays
the final multiply/subtract, giving the same total. This includes the
single-group anchor case and all group orders.

Every changed private node remains a nonzero linear form in the selector
hats. Its propagated degree remains1; only the two deleted degree-one
entries disappear. The complete degree dictionary on all retained
registers is identical, including the guarded native norm cancellations.
Thus all factor weights, original residual bounds and group weights stay
unchanged.

For factor weights d_i, put w_j=sum_{i in group j}d_i and let r be the
maximum original residual bound. The objectives remain

    SOS: 2*max(r,w_1,...,w_g),
    anchor a: w_a+2*max(r,{w_j:j!=a}).                (3)

For reference, the equality bases have weights

    normalized:760,1804,416,974,345,345,5,7,14,22,3,3; r=7,
    ordinary:760,832,416,345,345,5,7,14,22,3,3;       r=690.

The unit choice inserts G's degree2 between the word and exponent
factors and leaves r unchanged. The preceding exact subset recurrence
enumerates every partition and every possible anchor for these weights.
For every one of those plans, (1) reduces its cost by the same2M and
(3) is unchanged. Therefore its minimum at each group count is exactly
the prior minimum translated by−2 operations. Dominance between plans
and bases is preserved under this uniform translation. No additional
optimizer assumption or incomplete restriction to displayed winners is
used here.

The four resulting subfrontiers are:

|Strong / global treatment|Operation / degree points|
|---|---|
|normalized / unit|383/4714,385/4707,387/3608|
|normalized / equality|384/4712,386/4705,388/3608|
|ordinary / unit|384/4134,386/2900,388/2210,390/1664|
|ordinary / equality|385/4132,387/2900,389/2210,391/1664|

The degree floors are3608 for each normalized base and1664 for each
ordinary base, as in the prior exhaustive anchor-subset certificates.
They are attained at the endpoints above. Thus1664 is the minimum of
this four-base propagated objective, with no claim about another circuit
or an exact expanded polynomial degree. Retaining the equality option is
necessary for the nondominated385/4132 point.

## 4. Replay and evidence

The default checker recomputes all48 optimal group-count records using
the complete prior search, emits14 distinct frontier schedules, and
checks all nine selections of strong/global options. Every certificate
and full polynomial has exactly2M fewer than its matching prior plan,
unchanged A, and the same propagated bound. Twenty further ordered
four-group plans cover every anchor and SOS across all four bases.

The complete executions restore all22 old private values using the
guarded old local definitions, including the two deleted registers, and
compare every old full-source register. They also compare the factor and
group boundaries and independently assemble (2). Positive, signed and
zero-decoded-selector assignments are included. The normalized one-group
plans are additionally compared with the direct383/384 parent's outputs.

Author writer15608 and fresh50491 passed:68 complete opcode/degree/closure ledgers,
544 complete private-restoration, factor, parent and manual-finalizer
identities(272 signed),136 zero-selector cases,64 direct383/384
reassociation identities, and25 malformed callers rejected. All four
local links and source/note whitespace checks pass.

Native's independent full proof/source/dependency review and fresh19350
passed, with no remaining findings after the note-only API precision
correction in Section1. Its separate executor checked448 complete
manual-private/register/group/finalizer identities(224 signed) across
56 contexts:all48 winners and eight new reversed-five-group SOS/anchor4
plans. It included112 zero-selector cases and56 independent
degree/opcode/closure/domain checks. It transferred48 independently
established prior objectives and four floor certificates, reconstructed
all nine frontiers, and checked48 complete strong-correction maps
(24 signed) and48 global-slack maps(24 signed). All four local links and
whitespace checks passed. No source or receipt change was needed.

Root independently read the full proof, source and guarded family
dependencies; fresh26697 passed with no findings. The final source and
receipt are unchanged from the author and Native replays.

These finite assignments are algebraic fixtures, not materialized full
compiled Pell zeros. The proof of universality is the exact identity
with each selected reviewed parent and its unchanged program recipe.
