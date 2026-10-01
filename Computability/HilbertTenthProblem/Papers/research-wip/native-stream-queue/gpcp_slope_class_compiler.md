# Complete fixed-program compilation through slope classes

The [slope-class history](pcp_affine_slope_class_history.md) and
[factored transports](pcp_affine_factored_transports.md) now compose with
the full ordinary-input GPCP compiler. The default 34-tile odd-integer
example becomes **603=259M+344A** polynomial operations, with **98
positive witnesses**, **26 comparisons**, 526 certificate operations
and exact degree **6202**. The preceding complete unit source had918
operations,161 witnesses and degree19782. Thus all three measures
improve for this table.

The [source](gpcp_slope_class_compiler.py) and
[receipt](gpcp_slope_class_compiler.json) compare actual paid schedules
for every baseline pair and retain both per-tile layouts as fallbacks.
All candidates keep the same fixed tile table and ordinary-input
convention. The numerical example is decidable, not a universal table;
the separate universal75/88 frontier is unchanged.

## 1. A compiler choice with a complete theorem for every candidate

For a fixed affine table, the slope-class compiler retains one original
tile selector per tile, but only one selected-history value for each
nonbaseline slope class. If the table has s tiles and g exceptional
classes across its two coordinates, its scale exponent is N=s+g+4.
The omitted baseline contribution is supplied by the full history.
The component proof establishes one-hot control, range bounds, canonical
packing, exact selected updates and strictly positive completeness.

The compiler enumerates every upper/lower baseline pair occurring in
the actual table. Each candidate is emitted in full, then optionally
passed through the exact linear-form optimizer. It also emits both
original per-tile layouts, with the same optional optimization. It
chooses by actual operation count, then witness count, scale exponent
and multiplication count. This is a finite compiler search over fixed
data, not a runtime existential choice or an uncharged arithmetic gate.

Every candidate represents the same relation: a common nonempty tile
word takes `(1,Vinitial)` to `(Ufinal,Vfinal)`. Different packing choices
may require different native witnesses. Their positive input projections
agree; their polynomials are not asserted identical. Within a chosen
candidate, transport factoring is the exact all-integer polynomial
identity proved in its own packet.

`history_choice='per_tile'` and `'slope_classes'` expose the alternatives;
`factor=False` retains literal unfactored transports. The receipt keeps
every candidate ledger. The automatic result is no worse in arithmetic
count than the previous factored per-tile compiler for the same table.
No global arithmetic-circuit minimum is claimed.

## 2. Complete input and native-unit composition

The history replacement API checks that the actual affine table and
parameter names match the complete parent. It preserves the input
loader, boundary source and boundary comparisons literally; every new
history register and witness is prefixed. The three endpoint values are
the only shared history parameters. The input and computation packing
durations remain independent.

With a computed initial endpoint, its positive framing expression is
substituted in the history before native-unit projection. The two
explicit coordinate transformations then operate on the same three
native cores as before. The grouped history supplies their required
pretyping positivity even when g=0. All strong comparisons and ratio
slacks are retained. The optional regrouping includes nine sign-safe
norms and just the recoder checksum, while the history checksum remains
separate. The two unrestricted checksums are never merged without
their sign controls.

The complete parent theorem therefore composes directly: from a positive
zero, recover the padded input word, the common nonempty tile word, the
fresh-delimiter equation and an accepting computation. Conversely an
accepting computation gives an input recoder extension and a separately
chosen grouped history extension. Its new native scale receives fresh
positive witnesses. The source does not reuse the former per-tile native
tuple at the reduced scale.

The fixed machine must ignore **every** permitted leading-zero padding.
The paid loader `N=program_code*(2*x+1)` still adds three operations,
and its fixed-numeral specialization adds two. Selecting
`program_code=2^p` for a fixed universal interpreter yields every
recursively enumerable positive-integer language, exactly as in the
[complete parent](gpcp_complete_fixed_program.md). That interpreter
table is effective but remains numerically unspecified in this packet.

## 3. Counts for the chosen grouped source

Let C be the selected raw history certificate count after any transport
factoring, and let ell(k) be the paid power-chain length at input symbol
width k. When the selected history is the grouped one, the counts before
an optional program loader are:

| Version / initial endpoint | Certificate | Comparisons | Positive witnesses | Polynomial |
|---|---:|---:|---:|---:|
|Raw / supplied|C+134+ell(k)|55|s+g+79|C+298+ell(k)|
|Raw / computed|C+134+ell(k)|54|s+g+78|C+295+ell(k)|
|Units / supplied|C+143+ell(k)|27|s+g+60|C+223+ell(k)|
|Units / computed|C+143+ell(k)|26|s+g+59|C+220+ell(k)|

For the odd-integer table, s=34 and g=5. All twelve baseline pairs
are compiled; the winning pair is `(4096,4096)`. Its unfactored raw
history costs415, while the factored one costs381. The factored complete
alternatives are:

| Version / initial endpoint | Certificate | Equations | Witnesses | Polynomial | M+A | Degree |
|---|---:|---:|---:|---:|---|---:|
|Raw / supplied|517|55|118|681|279M+402A|1048|
|Raw / computed|517|54|117|678|278M+400A|2596|
|Units / supplied|526|27|99|606|260M+346A|2608|
|Units / computed, default|526|26|98|603|259M+344A|6202|

Without factoring, the corresponding computed-endpoint polynomials
cost712 raw and637 with units. The per-tile factored fallback still
gives814 with units,161 witnesses and degree19782. All of these
alternatives remain reproducible.

## 4. Exact degrees and verification

The existing literal degree audits run on every new complete source.
With the actual selected N, the raw degrees are

    supplied initial endpoint: max(24N+16,2k+2),
    computed initial endpoint: 12(k+1)N+16.

For the projected regrouped source, put e=1 for a direct/fixed input
loader, or e=2 for a free program parameter; v=(k+1)e+1;
nu=ke+1 if the initial endpoint is computed, otherwise2; and d=N*nu.
The exact degree remains

    14e+19v+20d-6nu+84+8*max(d,v).

Its proof depends on the literal scale and top/range regions, which the
grouped compiler retains. It includes the main-norm leading cancellation
and every actual coordinate projection. No zero-set power relation is
used to lower a polynomial degree. The raw and unit assertions also
cover g=0 and the smaller minimum exponent N=5.

The default replay checks432 complete raw residual/SOS identities and
432 complete native-unit restoration/output identities, half on signed
assignments. It records82 complete degree ledgers over singleton,
equal-slope and mixed-slope tables, both endpoint conventions, two widths
and all loader choices. Twenty-seven genuine outer machine/word/matrix/
grouped-history runs include accepting and rejecting inputs and
nondefault program parameters. Native Pell coordinates remain explicit
placeholders in these finite outer runs; their positive existence is
supplied by the component theorems, not inferred from the fixtures.

The acceptance equivalence, all runtime arithmetic and all witness
domains are complete. Numerical universality for a specified small
universal table and a reduction below the separate75/88 bounds are
additional research tasks.

Independent review passed the complete proof, source and fresh default
replay. Another96 independently assembled boundary/history residual and
SOS cases across twelve new numeric tables and loader choices passed,
including48 signed assignments and checks of the actual minimum among
the emitted candidates.
