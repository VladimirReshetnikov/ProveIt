# The query residue gives a378-operation universal polynomial

The [complete source](tseytin_query_unit378.py) turns the last ordinary query
comparison of the [lower-transport380 compiler](tseytin_lower_transport_unit380.md)
into an integer unit. The default complete polynomial costs **378=175M+203A**,
with377 certificate gates, one comparison,62 positive witnesses, one fixed
positive program parameter and ordinary positive input. Its degree is
**at most4713**. The [receipt](tseytin_query_unit378.json) stores all eight
global/equality, merged/separate and anchor/SOS schedules.

On valid recompiled program slices, the full supplied positive zero sets
are identical to380, with every coordinate unchanged. The initial coordinate
continues to mean the literal query encoding minus one; this packet does not
add another coordinate shift. The complete polynomials differ off zero.
The separate75-certificate/87-polynomial bound remains unchanged.

## 1. Fold a constant into the paid query numerator

Write d=8^64−1 and I=`c2_initial`. In380, the paid query is

    N(A,Q)−d=d*I, I=enc(query #)−1.                  (1)

Its left side is `query_numerator=query_last_product−C`, where C is already
the shifted fixed constant of380. Replace C by C−1, at the same one-subtraction
cost, and append

    R=query_numerator−query_scaled_word
     =N(A,Q)−d+1−d*I.                              (2)

Multiply R into the word-unit product and remove the ordinary query comparison.
Only the current numerator register changes; it has no other source consumer.
The constructor checks the entire canonical380 source and its actual fixed
constant, denominator, shifted initial interface, comparison and product ports.
Its current metadata explicitly records the extra1 in the numerator. Parent
records retain their historical meaning.

The default380 source has375 certificate operations and a five-operation
finalizer U*(1+qres²)−1. The new certificate adds one subtraction and one
multiplication. Since no ordinary comparison remains, its complete polynomial
is simply

    F=U*R−1.                                        (3)

It costs377+1=378. There is no emitted multiplication by1 or empty sum of
squares. The source handles this case explicitly. The squared version of(3)
costs379 operations. With remaining ordinary or separate-power comparisons,
the existing finalizer is retained and the saving is one addition.

|Global bound|Power products|Finalizer|Operations|M|A|Certificate|Comparisons|Degree bound|
|---|---|---|---:|---:|---:|---:|---:|---:|
|unit|merged|product minus1|378|175|203|377|1|4713|
|unit|merged|SOS|379|176|203|377|1|9426|
|unit|separate|anchor|381|176|205|376|2|4767|
|unit|separate|SOS|381|176|205|376|2|9318|
|equality|merged|anchor|380|176|204|375|2|4715|
|equality|merged|SOS|380|176|204|375|2|9422|
|equality|separate|anchor|382|176|206|374|3|4765|
|equality|separate|SOS|382|176|206|374|3|9314|

All forms retain62 positive witnesses. Their fixed program numeral and ordinary
input interface are unchanged.

## 2. Use the signed exponent theorem before any query interpretation

At a zero of any displayed finalizer, each constrained integer product is1
and all retained ordinary residuals vanish. Every individual factor, including
R and all six exponent factors, is therefore an integer unit. The exponent
subproduct E can initially be either+1 or−1; no prior query equality or history
sign is assumed.

The complete [exponent52 signed theorem](pell_fixed_affine_exponent52.md#2-norm-signs-and-the-plus-congruence-rank-argument)
starts with exactly E=±1. Its four norms exclude−1 independently modulo4. Its
rank and double-index argument forces the linear sign positive without using
the total-product sign. It then proves

    E=epsilon, Q=2^(96x+2epsilon−2), epsilon=±1.      (4)

Thus the only possible powers are2^(96x) and2^(96x−4). All51 renamed source
rows of this component and all six factor names are unchanged here. In a
separate-power schedule E=1 was already an ordinary product condition, but
the signed argument covers the merged schedule as well.

Let R=sigma=±1. Reducing(2) modulo d gives

    N(A,Q)=sigma−1 modulo d.

Its allowed residues are **0 and d−2**. On a valid program recipe, the two
parity-dependent residues at the wrong power in(4) are the exact values from
[permuted-digits387, Section3](tseytin_permuted_digits387.md#3-the-paid-query-and-its-sign-filter):

    29966043244819123951156626953424814080,
    45854471631935696494459945720637767680.           (5)

Both are strictly between0 and d−2. One direct closed form, with B0=2^96,
is24*(15759360 B0+558888960) for even x and
24*(24115200 B0+550533120) for odd x. Subtracting d for the inherited initial
shift changes neither residue. Consequently the wrong exponent branch is
impossible even though the query was initially only a signed unit.

Therefore E=1 and Q=2^(96x). The valid program recipe then gives
N(A,Q)=d*enc(query #), so its residue is0. Since d>2, this forces sigma=1.
Equation(2) now restores the exact old query(1).

This argument precedes every history, global-bound and transport interpretation.
In particular it does not import380's use of the ordinary query to force the
exponent sign: (4) is the stronger signed theorem, and(5) is the separate exact
modular exclusion needed for the new factor.

## 3. Restore the full parent on identical supplied coordinates

With R=1, the new product conditions reduce to the old word/power products.
Every retained ordinary condition is unchanged, and the removed query condition
has just been proved. Thus every positive new zero on a valid program slice
is a positive380 zero on the identical tuple. That parent theorem restores
the native, upper/lower and global signs and its exact accepted-input relation.

Conversely every positive380 zero already satisfies(1), hence has R=1, and
all new product and ordinary conditions hold with no coordinate changes.
This proves full positive-zero equality on valid program slices. The affine
initial shift belongs to the preceding380-to381 map; composing the two steps
still changes that coordinate only once. No equivalence is asserted for
arbitrary invalid program coefficients.

## 4. Full-output corrections, degrees and verification scope

At arbitrary supplied integers, let U be the old complete product in the
merged form, or the old word product when separate. Let Splus be the sum of
the remaining ordinary residual squares, including the separate exponent
product residual if present. The old query residual is R−1. The old and new
anchor expressions are

    U*(1+Splus+(R−1)²)−1, U*R*(1+Splus)−1.

Their difference is U(R−1)(Splus−R+2). This identity includes Splus=0,
where the new source emits(3) directly. The corresponding SOS difference is
U²(R²−1)−2U(R−1)−(R−1)². The checker verifies these complete corrections,
the manual finalizers and every retained register, accounting explicitly
for the changed numerator and merged product.

The query factor has degree bound7. The default380 product had bound4706;
its new product therefore has bound4713. Its last residual square, which
formerly added14, is gone. The guarded native and exponent norm cancellations
are unchanged. The other table entries follow from the literal propagated
degrees. These are upper bounds; no expanded-degree or general circuit
minimum is claimed.

Every emitted gate reaches the complete output. Canonical guards include
source, active interfaces, program recipe, factors, comparisons and semantic
scope; Boolean mode checks precede caching. The exact two-parity modular
certificate proves the residue exclusion for every positive input on valid
program slices. Finite source and literal-query fixtures check implementation
details and do not materialize full compiled Pell zeros.

Author writer42885 and fresh93159 passed:192 retained-register maps
(96 signed),384 complete output corrections(192 signed),16 zero-selector
contexts, all eight ledgers,51 unchanged exponent rows,80 literal queries
and both exact modular residues. Native's independent full proof/source/
dependency review and fresh49432 passed with no findings. Its separate
interpreter derived the degree6 numerator from actual repeat/append maps,
checked both excluded residues, two symbolic finalizer corrections,
160 retained-register maps(80 signed),320 complete output corrections
(160 signed),32 zero-selector contexts, all eight degree/opcode/domain/
liveness ledgers,126 independently encoded queries and73 malformed callers.
All five local links and whitespace passed. Gibbs separately checked the
signed-exponent dependency and exact residue mechanism before authoring;
none of these finite checks is presented as a full native Pell-zero fixture.
