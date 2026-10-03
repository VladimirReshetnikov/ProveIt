# A complete 418-operation universal source by repunit sharing

The [literal source](tseytin_repunit_sharing418.py) saves seven operations
in the [complete425 source](tseytin_universal425.md), giving
**418=194M+224A**,398 certificate gates, seven comparisons and65 positive
witnesses. It has the same ordinary positive input, single fixed positive
program parameter, complete integer polynomial, and degree bound5868.
The separate-unit form costs420=194M+226A with degree bound5814.
Both SOS finalizers and their literal sources are included in the
[receipt](tseytin_repunit_sharing418.json).

This is an exact source identity on the identical supplied coordinates.
Every positive zero, every valid program slice and the effective
universality theorem are inherited without a new native sign argument
or endpoint assumption. The overall75-certificate/87-polynomial record
is unchanged. No global arithmetic optimality is asserted.

## 1. Reuse the paid eight-term repunit and two powers

Write P for the graph register `P__30` and

    R_m(P)=1+P+...+P^(m−1).

The parent already computes all of

    repunit_product__253=R_8(P)=(1+P)(1+P²)(1+P⁴),
    P8__277=P⁸, P16__279=P¹⁶.

These values serve the eight physical-selection lanes and the larger
controller/range geometry. Their entire defining subgraph is retained.
Independently, the parent computes its24-term controller repunit as

    R_24(P)=(1+P+P²)(1+P³)(1+P⁶)(1+P¹²).

Beyond the paid P and P², that branch uses ten rows: three powers P³,
P⁶,P¹²; four additions for the factors; and three products. Its only
externally consumed result is `repunit_product__215`.

Use instead the polynomial identity

    R_24(P)=R_8(P)(1+P⁸+P¹⁶).                         (1)

The three new rows are exactly

    c2_repunit_outer_pair=P8__277+P16__279,
    c2_repunit_outer_factor=c2_repunit_outer_pair+1,
    repunit_product__215=repunit_product__253*c2_repunit_outer_factor.

For each exponent0<=e<24 there is exactly one representation
`e=i+j` with0<=i<8 and j in{0,8,16}. Expanding the right side of(1)
therefore gives coefficient1 at every exponent0,...,23. This proves(1)
for every integer P, including0,1 and negative P; no division by P−1
or positive-solution relation is used.

The former ten rows cost6M+4A. The new three rows cost1M+2A, so the
literal saving is **5M+2A=7 operations**. The two new temporary names
replace nine erased private register names; the final repunit name and
all its consumers are unchanged.

## 2. Privacy, ordering and complete source equivalence

The nine erased registers are

    repunit_tail__206, P3__207, repunit_factor__208,
    repunit_product__209, P6__210, repunit_factor__211,
    repunit_product__212, P12__213, repunit_factor__214.

Their consumers all lie in that same branch or are its retained final
product. The checker requires these exact consumer sets and rejects any
additional use. It also recursively rejects these names in any non-source
packet field, including nested export keys and values. None is an active
interface, factor, comparison or supplied coordinate in the canonical
parent. Their historical values can be recovered by the explicit
`restore_registers` diagnostic formulas; this is not a new witness map.

The paid P⁸ and P¹⁶ occur later in the old row order. Their ancestry is

    P²=P*P, P⁴=P²*P², P⁸=P⁴*P⁴, P¹⁶=P⁸*P⁸.

The paid R_8 depends only on P,P²,P⁴. Thus neither new operand depends
on the old R_24 branch, and the replacement introduces no cycle. The
builder performs a stable topological sort and checks the complete
declared-input closure. Every final source gate remains live.

On an arbitrary supplied integer assignment, the retained input
registers have identical values. Identity(1) gives equality of the
retained R_24 register, and induction through the common dependent graph
gives equality of every other retained register. In particular all word
and exponent factors, all ordinary residuals and the query loader agree.
The finalizer is unchanged, so each complete polynomial agrees at every
integer assignment, for both merged/separate products and both SOS
finalizers. All65 positive witness coordinates and both input/program
parameters are identical. Consequently the positive-zero correspondence
is the identity, even away from valid program slices; the inherited
interpretation as a universal input relation retains the parent's valid
program-slice hypothesis.

## 3. Literal cost and degree

| Form | Certificate | Comparisons | Witnesses | Polynomial | M | A | Degree bound |
|---|---:|---:|---:|---:|---:|---:|---:|
|Merged product|398|7|65|418|194|224|5868|
|Separate product|397|8|65|420|194|226|5814|
|Merged SOS|398|7|65|418|194|224|11460|
|Separate SOS|397|8|65|420|194|226|11352|

Every numeral operation remains charged. The finalizers are identical
to their matching parents, so the same−5M−2A change applies to all four
complete schedules.

The source computes P with propagated degree2. Both implementations of
R_24 have propagated degree46: the new one has R_8 degree14 and
`1+P⁸+P¹⁶` degree32. The checker compares the propagated degrees of
every retained source register, not just the final repunit. Both literal
main-norm cancellation graphs are unchanged. Their exact arbitrary-value
identities, and hence the entire parent degree dictionary, still apply.
The word factor bounds remain931,2158,503,72,1154,429,429, and the
exponent factor degrees remain5,7,14,22,3,3. The largest residual bound
remains69. These are the same propagated universal degree bounds as the
parent; exact expanded universal degree is not claimed.

## 4. Guarded API and reproducible evidence

`build(merge_units=True)` emits the default. `rewrite(old)` requires the
entire canonical425 parent, including the supplied domains, program
recipe, comparisons and metadata. The complete polynomial and degree APIs
likewise reject altered successor packets. The local `rewrite_rows(old)`
only promises the checked graph identity; a different compiler or
partition family must independently establish its complete canonical
host and theorem before using that helper.

The local guard checks19 literal defining rows: the old repunit24 branch,
the paid repunit8 branch and its shared powers through P¹⁶. It verifies
all nine erased consumer sets, all non-source exports, fresh temporary
names, source closure and the exact multiplication/addition delta. The
receipt also expands(1) as an exact24-entry coefficient vector.

Run `python tseytin_repunit_sharing418.py` for a fresh receipt comparison;
`--write` regenerates the receipt. The checker exercises both canonical
parents and both finalizers, verifies192 complete retained-register and
manual-restoration maps (96 signed), and384 complete polynomial identities
(192 signed). Four assignments have every decoded selector zero, so
P=1 is explicitly included. It checks all four literal operation/degree/
liveness ledgers and23 malformed local/canonical callers. These are
arbitrary-integer source identities, not materialized full giant Pell
zeros. Author generation and a separate fresh default replay pass; all
three local links and the trio's whitespace check pass. Root independently
replayed the committed receipt. A separate full proof/source review passed
with no findings, including256 complete retained-register maps,512
parent/manual-finalizer output identities(256 signed assignments),16
zero-selector contexts, all four degree/liveness ledgers, eight symbolic
and corner repunit checks, and41 malformed-host rejections. These are
source/component identities, not exhaustive native Pell-zero tests.
