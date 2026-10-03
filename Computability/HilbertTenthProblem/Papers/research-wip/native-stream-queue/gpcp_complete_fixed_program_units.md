# Native-unit reductions in the complete fixed-program compiler

The [complete fixed-program GPCP compiler](gpcp_complete_fixed_program.md)
admits a **75-operation reduction** in its final polynomial, with nineteen
fewer positive witnesses. This combines the [recoder unit projection](native_binary_input_dilation_unit179.md)
and the [affine-history unit projection](pcp_uniform_affine_pair_units.md)
on their actual disjoint native cores. All ordinary-input, framing,
unbounded selection, geometry, range and transport obligations remain paid.

For the illustrative 34-tile odd-integer machine, the default becomes
**918=403M+515A**, with **161 positive witnesses**, **26 comparisons**,
841 certificate operations and exact total degree **19782**. The raw
993-operation, degree8416 source remains a lower-degree alternative.
The numerical example is not a universal table. The effective universal
interpreter and paid program loader are inherited from the complete
parent; no change to the independent universal75/88 frontier is claimed.

The [source](gpcp_complete_fixed_program_units.py) exposes both successive
coordinate maps and a safe regrouping of norm factors. The
[receipt](gpcp_complete_fixed_program_units.json) records the full source,
literal ledgers, arbitrary signed identities and exact degree audits.

## 1. Two complete coordinate changes

First apply the recoder rewriter to the complete parent, using only its
`geo__` and `and__` cores. It changes two positive first-root coordinates,
projects thirteen positive definitions and merges six sign-safe norms
with the recoder-AND checksum. It adds six product multiplications and
removes nineteen comparisons. Its remaining comparison system includes
every history comparison unchanged.

Then apply the one-core history rewriter with prefix `hist__and__`.
It changes its positive first root, projects six positive definitions
and merges three sign-safe norms with the history checksum. It adds
three product multiplications and removes nine comparisons. The two
rewrites therefore give

    certificate operations: C_raw+9,
    comparisons: e_raw-28,
    positive witnesses: w_raw-19.                         (1)

Each source retains both ratio slacks and its complete strong equality.
The auxiliary norm uses the paid strong right side, with the independent
modulo-four sign proof; its old coefficient is restored by that equality.
The input and history geometries remain separate.

The composition also works with the paid loader. Its loaded integer is
positive for every positive x and program_code, so projecting
`q=loaded_input+input_slack` preserves the recoder's pretyping positivity.
For a computed initial endpoint, the positive framing expression then
supplies `Vinitial`. The history's computed J is nonnegative and P>=1
on positive assignments even before its comparisons. Its hatted selector
packs decode to nonnegative words, making the projected native packing
index positive before the AND theorem.

The explicit new-to-old map first restores the history coordinates, then
the recoder coordinates. The reverse map applies the recoder projection
first, then the history projection. At zeros, the norm signs force the
three gaps to be odd, giving strictly positive integral old roots.
These maps are inverse. Away from zeros their rational versions still
give the checked literal residual identities; even gaps give
half-integral old roots and are not claimed to be integer kernel inputs.

## 2. Safe regrouping leaves one checksum outside

There are nine norm factors: three from each native core. Every one
independently excludes -1 modulo4 on all integer assignments, before
any typing or strong-equality substitution. There are also two
checksum factors, C_rec and C_hist. No such sign exclusion is asserted
for either checksum.

The separate arrangement keeps the two unit comparisons

    U_rec=(six recoder norms)*C_rec=1,
    U_hist=(three history norms)*C_hist=1.                 (2)

The default regrouping instead keeps

    U_all=(all nine norms)*C_rec=1,
    C_hist=1.                                             (3)

Equation U_all=1 forces its ten integer factors to be units. The nine
independent sign exclusions make every norm1, and then C_rec=1. The
second comparison gives C_hist=1. Hence (3) implies both comparisons
in (2). Conversely (2) forces all nine norms and both checksums1,
so it implies (3). This is an equivalence in the actual supplied integer
coordinates, independent of the later positive-root restoration.

Multiplying U_rec and U_hist alone would not justify this argument:
it could leave both unrestricted checksum factors equal to -1. The
compiler deliberately retains the second checksum as an explicit
comparison. It asserts that the old product-chain registers have no
other consumers before replacing them. The old chains used6+3=9
multiplications; the new ten-factor chain uses9. The operation and
comparison counts therefore do not change under regrouping.

With R_i the remaining comparison residuals, the final polynomial is

    F=U_all*(1+sum_i R_i^2)-1.                             (4)

Its zero set forces the positive integer `1+sum R_i^2` and U_all both
to be1. Thus every outer comparison holds, including C_hist=1, and
the preceding argument restores the complete parent. The separate
option uses U_hist in (4) and keeps U_rec=1 among the squared residuals.
Both options have the same paid operation count but different degrees.
Regrouping is not asserted to improve degree for every possible table.

## 3. Literal costs

The product finalizer costs `3e-1` operations for e comparisons,
exactly the parent's SOS finalizer cost. Applying (1) therefore changes
the complete polynomial cost by `9-3*28=-75`, including fixed-numeral
products and every residual subtraction.

Write H for the raw history certificate cost, s for its fixed tile
count and ell(k) for the paid power-chain length at symbol width k.
Before an optional program loader, the exact ledgers are:

| Initial endpoint | Certificate | Comparisons | Positive witnesses | Polynomial |
|---|---:|---:|---:|---:|
|Supplied|H+143+ell(k)|27|3s+60|H+223+ell(k)|
|Computed, default|H+143+ell(k)|26|3s+59|H+220+ell(k)|

The free program loader adds3=1M+2A; the fixed-numeral loader adds
2=1M+1A. It adds no positive witness or comparison. The free inputs
are x, and program_code when present.

For the odd-integer example at k=4,s=34, the regrouped alternatives are:

| Layout / initial endpoint | Certificate | Equations | Witnesses | Polynomial | M+A | Degree |
|---|---:|---:|---:|---:|---|---:|
|Contiguous / supplied|844|27|162|924|408M+516A|6136|
|Contiguous / computed|844|26|161|921|407M+514A|15022|
|Interleaved / supplied|841|27|162|921|404M+517A|8040|
|Interleaved / computed, default|841|26|161|918|403M+515A|19782|

The separate-unit default-layout version also costs918, at degree20310.
These are specific source schedules, not minimum-operation claims.

## 4. Exact degree after all projections

Degrees must be recomputed: in this source q is a computed expression,
so the free program parameter changes its degree. Set

    e=1 for direct input or a fixed program numeral,
    e=2 for the varying program_code loader,
    v=(k+1)e+1,
    nu=ke+1 if Vinitial is computed, otherwise nu=2,
    d=N*nu,

where N=3s+4 or4s+4 for the two layouts. The native scales in the three
cores have degrees e,v,d respectively. The ten regrouped factor degrees
in their literal source order are

    5e+7, 6e+12, 3e+5,
    5v+7, 10v+8, 3v+5, v,
    5d+7, 12d-6nu+8, 3d+5.                               (5)

In particular, the geometry core's auxiliary U is dominated by j*c;
the recoder AND's packed r has degree3v+1; the history AND's packed r
has degree4d-3nu+1. These are different degree calculations even
though the kernels have the same shape.

There is one mandatory cancellation in each main norm. With
`d_native=X+a*c+G` and `G=ga*(4a+3)`, the source's norm expands exactly as

    d_native^2-(a^2+4a+3)c^2
      =X^2+2Xac+2XG+2acG+G^2-(4a+3)c^2.                 (6)

The unique highest term is `2acG`, whose highest form is
`8*ga*a^2*c`. The degree audit checks every source prerequisite of
(6), proves all its other terms strictly lower, and then propagates
its exact leading form. This is a degree proof about the literal
computed polynomial, not an additional runtime gate or a zero-set
substitution. Every other propagation uses the actual source arithmetic.

The degree of U_all is

    14e+19v+20d-6nu+64.

The largest outer residual degree is `4*max(d,v)+10`, attained by a
retained strong equality. The max is necessary for very large k with
a supplied initial endpoint. Hence the exact degree of (4) is

    14e+19v+20d-6nu+84+8*max(d,v).                        (7)

The audit evaluates the leading homogeneous forms at a positive weight
vector, with root-gap weights chosen to avoid cancellation. The unit
leading coefficient and the leading sum of squares are nonzero, proving
attainment of the displayed upper degree. Only bit lengths, signs and
hashes of the large coefficients are serialized. The source separately
checks all ten formulas (5) and the final formula (7).

The separate-unit option has exact degree
`21d-6nu+20+2*max(14e+19v+44,4d+10)`, also asserted against
the literal source. Its recoder unit residual can dominate the outer
sum when the input alphabet width is large.

For the default odd-machine layout, the direct-input degree is19782;
keeping the initial endpoint supplied gives8040. With a free program
parameter and computed initial endpoint the degree is35547. None of
these calculations treats the loader as a degree-one free input after
its actual substitution.

## 5. Reproduction and scope

The default checker replays384 complete restored-parent polynomial
identities, including192 signed cases, across48 compiler variants.
It verifies both directions of the rational coordinate maps, the
strong-equation correction to every changed auxiliary norm, every
remaining residual and both finalizer arrangements. Fifty-nine literal
degree ledgers include the eight full odd-machine alternatives and
three width100 singleton cases with different program loaders.

The positive-zero theorem follows from the complete parent and the
three explicit positive-coordinate proofs. No new numerical Pell
extension is claimed by these algebraic fixtures. The compiled table
and polynomial remain fixed for any chosen Turing machine, and the
parent's three-operation universal-interpreter loader remains valid.
An explicit numerical universal interpreter table, a better75/88
bound, and a Lean formalization are separate tasks.

Two independent source reviews passed after the author replay. One added
288 signed direct-formula complete-output checks and four exact
weighted-offset degree audits, including a free program parameter and
a large-width supplied endpoint, then reviewed the final proof and
default replay. The other added288 direct-norm/full-output checks,
including144 signed cases, over new singleton and multi-tile tables
and all composition options. Neither review found a remaining issue.
