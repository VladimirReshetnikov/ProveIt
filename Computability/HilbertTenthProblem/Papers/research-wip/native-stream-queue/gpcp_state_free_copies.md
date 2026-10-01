# State-free copied contexts in the fixed-machine GPCP compiler

The fixed-machine compiler can omit every copy tile for a control state.
It retains the full symbol alphabet, its codes, the symbol width, every
rewrite rule, and the ordinary-input boundary. The default odd-integer
example falls from34 to30 tiles and from603 to **587=254M+333A** polynomial
operations, with **94 positive witnesses**,26 comparisons,510 certificate
operations and exact degree **5642**. The former example used98 witnesses
and degree6202.

The [source](gpcp_state_free_copies.py) and
[receipt](gpcp_state_free_copies.json) are a separate successor to the
[complete slope-class compiler](gpcp_slope_class_compiler.md). Earlier
defaults and receipts remain unchanged. This generalizes the deletion
already used by the separate [explicit Neary–Woods construction](neary_woods_explicit_universal_tm.md);
it does not change that construction or the universal75/88 bounds.

## 1. Which copied symbols are necessary

Let Gamma be the fixed tape alphabet, Q the disjoint state alphabet, and
`[`, `]`, `#` three fresh delimiters. Keep the original alphabet

    A = Gamma union {[, ], #} union Q

and every original digit code. The compiler retains copy tiles `(a,a)`
only for `a in Gamma union {[, ], #}`. It retains every transition,
tape-extension and accepting-cleanup rewrite tile.

A well-formed configuration has its two outer brackets, no `#`, and
exactly one state. Each transition-rule left side contains that state
once, and its right side contains the new state once. This includes the
rules extending either end of the bounded tape. The cleanup rules
`accept a -> accept` and `a accept -> accept` also consume the sole state
once and preserve it once.

Consequently, if `w = u l v -> u r v` is any genuine transition or cleanup
step, both copied contexts `u` and `v` contain only tape symbols and
brackets. Its usual tile row uses the retained copies for `u`, the
retained rule tile `(l,r)`, then the retained copies for `v`. Between
rows the retained `(#,#)` copy separates successive configurations.
Every nonempty derivation is therefore encoded with exactly the same
two concatenated words as before.

Conversely, each retained tile is a tile of the old table. Replacing
each new tile ID by its explicit old ID preserves both words on every
selection, whether or not it encodes a valid history. Thus a new GPCP
solution is an old GPCP solution. On a valid initial configuration, the
old fresh-delimiter theorem supplies an accepting derivation. This
argument does not need to normalize arbitrary old tile witnesses or
copy-only rows: completeness rebuilds a selection directly from the
genuine derivation.

The compiler requires `start != accept`. A derivation from its initial
configuration to `[accept]` cannot then be reflexive, so its completeness
selection is nonempty. The empty tile word also cannot satisfy the framed
word equation: its left side begins `#`, while the initial word begins
`[`. The helper explicitly refuses to copy a zero-step configuration
containing a state, since such a copy is exactly what was removed.

The two tables therefore have the same acceptance predicate on the
well-formed start configurations under discussion. The subset direction
holds for arbitrary boundaries, but the converse is not asserted for
malformed tuples, arbitrary state words, or a reflexive accepting start.

## 2. Ordinary input and all positive arithmetic interfaces

`build_for_tm` has the original fixed-machine interface. It obtains the
canonical full alphabet and codes, forms the reduced table, then invokes
the existing complete raw history/compiler followed by the chosen
slope-class, transport-factoring and unit transformations. Its options
include raw versus unit source, supplied versus computed initial value,
per-tile versus slope-class history, and all original program loaders.
`odd_machine` preserves even the historical machine's state names and
digit assignments.

The input prefix, suffix, terminal word, width, input-recoder source and
loader source are unchanged literally. The original tile-ID embedding
is supplied in the packet and checked against both symbolic tile words.
The code does not renumber the symbol alphabet when it drops tile IDs.
In particular, the ordinary input still decodes to the same padded binary
word. As before, a fixed machine representing a language of ordinary
integers must ignore **every** permitted leading-zero padding. This
condition is a hypothesis of the language theorem, not a property the
finite table constructor decides.

The reduced affine table has positive integer slopes and nonnegative
offsets. Its complete history theorem pays all selector typing, selected
products, range bounds, common geometry and transports. On an accepting
computation, rebuild its reduced selection and then choose fresh positive
history and native witnesses. The smaller packing scale is not supplied
with the old table's native tuple. Conversely, a positive arithmetic zero
gives a common nonempty reduced tile word, which embeds into the old word
equation and hence gives acceptance on the valid initial configuration.

The optional native-unit compiler retains its three separate native
cores and their strong comparisons. Its global product still has nine
sign-safe norms and only one unrestricted checksum; the other checksum
remains explicit. All original positive-coordinate proofs therefore
apply unchanged to the newly compiled table. This is equality of
accepted-input projections, not an all-assignment polynomial identity or
a bijection between the old table's and new table's auxiliary tuples.

The paid loader `program_code*(2*x+1)` and its fixed-positive-numeral
specialization remain available at their existing costs. Any fixed
leading-zero-stable universal interpreter with distinct initial and
accepting states inherits the deletion theorem. This packet's numerical
examples are decidable finite machines; the existing explicit universal
Neary–Woods packet already performs its own state-copy deletion.

## 3. Counts and exact degrees

If there are q state symbols, p tape symbols and R rewrite rules, the
copy count falls from `p+3+q` to `p+3`, and the total tile count falls by q.
Every copy tile has the same slope pair `(2^k,2^k)`. Tape and delimiter
copies remain, so the sets of upper and lower slopes do not change.
Consequently the grouped compiler's exceptional-product count
`g=du+dv-2` is unchanged, while its exponent `N=s+g+4` falls by q.
The actual paid history cost H is compiled and scored again; no uniform
gate saving is assumed from a change in tile count alone.

For a selected grouped history, before an optional program loader the
complete counts remain:

| Source / initial value | Certificate | Comparisons | Positive witnesses | Polynomial |
|---|---:|---:|---:|---:|
|Raw / supplied|H+134+ell(k)|55|s+g+79|H+298+ell(k)|
|Raw / computed|H+134+ell(k)|54|s+g+78|H+295+ell(k)|
|Units / supplied|H+143+ell(k)|27|s+g+60|H+223+ell(k)|
|Units / computed|H+143+ell(k)|26|s+g+59|H+220+ell(k)|

Here `ell(k)` is the paid width power-chain length. Per-tile alternatives
retain their own actual source and witness ledgers; the automatic history
choice compares them with every paid slope-baseline pair. All candidates
represent the same reduced table, with no runtime choice variable.

For the odd-integer example, `s=30`, `g=5`, `N=39`, `k=4`, `ell(k)=2`.
The selected raw history costs365 operations. The factored results are:

| Source / initial value | Certificate | Polynomial | M+A | Comparisons | Witnesses | Degree |
|---|---:|---:|---|---:|---:|---:|
|Raw / supplied|501|665|274M+391A|55|114|952|
|Raw / computed|501|662|273M+389A|54|113|2356|
|Units / supplied|510|590|255M+335A|27|95|2384|
|Units / computed|510|587|254M+333A|26|94|5642|

The comparison with603 is for the same ordinary odd-integer language,
codes, framing and computed-endpoint convention. Four state-copy tiles
are removed; the new complete source saves16 operations and four
positive witnesses.

Other compiled test tables use the same direct-input, computed-endpoint,
factored-unit convention:

| Machine | Reduced tiles | Certificate | Polynomial | M+A | Witnesses | Degree |
|---|---:|---:|---:|---|---:|---:|
|Even-integer recognizer|30|513|590|256M+334A|94|5642|
|All-input right scan|21|445|522|234M+288A|85|4382|
|Right scan followed by left return|33|532|609|266M+343A|97|6062|

These figures are actual emitted sources for different decidable
languages and are not interchangeable universal bounds.

The exact degree is checked on every emitted source, including all
computed endpoint substitutions and paid loaders. For raw sources it is
`max(24N+16,2k+2)` with a supplied initial value, or `12(k+1)N+16` when
computed. For the regrouped unit source, put

    e = 1 for direct/fixed input, or 2 for a free program parameter,
    v = (k+1)e+1,
    nu = ke+1 with computed initial value, or 2 if supplied,
    d = N nu.

The exact degree is

    14e + 19v + 20d - 6nu + 84 + 8 max(d,v).

The inherited audit checks the actual norm leading cancellation, every
factor degree and a nonzero highest-form evaluation. It uses no equation
valid only on positive zeros to reduce the polynomial degree.

## 4. Verification scope

The replay checks192 complete raw residual/SOS identities and192 complete
unit restoration/product identities, half on signed assignments, for
four machine tables, both endpoint conventions, and per-tile, class-only
and automatic histories. These are identities for each emitted reduced
source against its own independently assembled complete component
formulas; the larger-table polynomial is not asserted identical.

There are330 local transition/extension/cleanup derivations, testing every
actual rule with several contexts. Full cleanup paths include tape on both sides of the accepting
state. Each selection is checked under the explicit embedding into the
old tiles, and independent dense affine append agrees with its endpoint.
The51 positive outer runs include odd, even and all-input machines, a machine
returning left across the input and extending the left boundary, extra
zero padding, and free/fixed program loaders. They check acceptance and
rejection at the terminal comparison where applicable, the first five
input-recoder comparisons, all three history transport/global-bound
comparisons, dense affine append and positivity of the fixture coordinates.
The remaining geometry/native comparisons are not asserted numerically
zero. Native Pell coordinates in these finite runs remain
placeholders: full positive existence follows from the complete component
theorems, not from the test fixtures.

The receipt records59 exact degree ledgers with their M/A counts and one
complete default source. No existing source, receipt or navigation file is changed.

The author writer and fresh default replay passed. Independent root
proof/source review passed with no findings; another64 signed complete
unit identities and216 manually assembled transition derivations on eight
random machine tables passed, varying tape/state cardinalities and both
endpoint conventions. Root's separate fresh default replay also passed.
