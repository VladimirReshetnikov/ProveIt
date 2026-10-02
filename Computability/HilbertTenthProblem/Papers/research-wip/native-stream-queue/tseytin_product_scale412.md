# A product scale gives a412-operation Tseytin universal polynomial

> The [reviewed global-unit successor](tseytin_global_bound_unit385.md)
> gives385 operations,62 witnesses and degree at most4714; its
> [four-base factor family](tseytin_global_unit_factor_partitions.md) reaches392/1664.
> Its encoding descends from the permuted-digit stage. The source, encoding
> and transfer proof below remain this frozen stage.

The [source](tseytin_product_scale412.py) removes three multiplications
from the [free-height415 compiler](tseytin_free_height415.md). The complete
universal polynomial has **412=191M+221A** operations,392 certificate
operations, seven comparisons,65 positive witnesses, one fixed positive
program parameter, ordinary positive input, and degree **at most5662**.
The separate-power form has414 operations and degree at most5608. The
respective SOS degree bounds are11052 and10944, at the same respective
operation totals. The [receipt](tseytin_product_scale412.json) emits all
four complete schedules.

This is a transfer of the established
[U9 product-scale argument](neary_woods_universal_product_scale253.md),
which itself adapts the [group scale construction](group_projective_product_radix_scale.md).
Its literal C2 application saves three private power gates. It preserves
the accepted ordinary-input relation on valid program slices by rebuilding
private native witnesses. The old and new complete polynomials need not
agree away from zero; no bijection of supplied native zero tuples is claimed.
The separate75-operation certificate bound is unchanged.

## 1. Reuse the paid history product

Use the parent's height D, history radix B, selector sum J and history
scale P. Put T=P^34; its two paid squares and underlying powers remain
in the literal source. The existing lower words H0,M0,Z satisfy

    H_old=H0+B*T, M_old=M0+(B−1)*T, q_old=16P^36.

Replace just these top definitions by

    H=H0+2T, M=M0+T, q=16B*T.                        (1)

The existing paid `top_history__285=B*P34__284` becomes the scale's
consumer. Replace the paid mask product by `top_mask__290=2*P34__284`;
H reads that product, and M reads the existing P34 register directly.
The paid multiplication by16 now reads `top_history__285`. Delete
exactly the three now-private products

    P9=P8*P, P18=P9², P36=P18².

P8 and P16 remain live, including in the shared length24 repunit.
Every fixed-coefficient multiplication remains charged. The graph is
topologically sorted and every remaining gate reaches the final output.
The canonical guards check the entire supported415 packet, the eight
literal source rows, private consumers, complete successor interfaces,
domains and program recipe. Historical parent records are provenance,
not the current native-scale interface.

## 2. Scalar bounds before any binary typing

At a positive zero every ordinary comparison holds. The unchanged
exponent52 projection and paid query comparison first give the positive
power-unit branch and restore the literal query, exactly as in the
[425 proof](tseytin_universal425.md). This does not use a native word
interpretation or any endpoint-height estimate. The remaining native
word-unit product consequently equals1.

The unchanged positive global comparison and exact repunit definition give

    P>=11, B=65536D>=65536, J>=0, P=(B−1)J+1.

Thus J>=1 and B<=P. Both history hats and all eight selected-product
hats are below P. Unhat products and selectors are nonnegative; each
selector-class mask is at most `(B−1)J=P−1`. The range coefficient is
`(D−1)J`, lying in[0,P). Therefore the parent's exact eight physical,
24 controller and two range lanes still fit in ordinary integer base P:

    0<=H0,M0,Z<T=P^34.                              (2)

This is a scalar statement; P is not yet assumed dyadic. It includes
D=1, when the range coefficient is zero. The two top lanes are no longer
used to establish (2). The resulting ports in(1) obey

    H−Z>=T+1, M−Z>=1,
    BT−H−M+Z>=(B−5)T+2>0,
    0<=H,M,Z<BT.                                   (3)

The actual native ports are `A=16H+12`, `C=16M+10`, `F3=16Z+8`,
with scale q=16BT. They are strictly positive and below q. The other
three native truth fields remain supplied positive coordinates; the
two unchanged comparisons identify `A=F1+F3` and `C=F2+F3` at a zero.
All ratio and strong-norm auxiliaries remain positive. The same literal
native bound is `X=q(r+beta)>r`, since q>=16 and r is a positive packed
index. No endpoint bound or exponent typing is used in these facts.

## 3. Type the product factors before splitting the top block

Apply the parent's complete local coupled-unit native theorem in exactly
its stated sign order. Its hypotheses are the positive prescribed ports,
positive supplied fields, q>=16, strict native bound, both retained ratio
slacks and the complete normalized strong equation. It does not require
the prescribed positive q to be a pure power of P. Thus it yields q dyadic
and the prescribed padded AND, equivalently `H AND M=Z`. The coupled
checksum/index negative branch, where present, is handled by that theorem's
private-coordinate restoration; we do not assert that every individual
word factor is+1 at every positive zero.

Now the *new paid identity* `q=16B*P^34` and positivity force both B and P
to be powers of two. This recovers B without an old `B AND(B−1)` top test.
Since B=65536D, D is dyadic too. The unchanged exact relation
`P=(B−1)J+1`, with J>=1, gives

    P=B^t, J=1+B+...+B^(t−1), t>=1.

Indeed `2^v−1` divides `2^u−1` precisely when v divides u. Consequently
T is dyadic and (2) gives the exact split

    (H0+2T) AND(M0+T)=(H0 AND M0)+T*(2 AND1)
                     =H0 AND M0.                  (4)

All lower lanes are unchanged. They recover one of the actual24 tiles
at each chronological row, the eight selected slope-class products and
both current digits in[0,D). The one-hot argument still uses24<B. It
also covers duration one B=P.

The fully paid query has base-eight digits1 through6 and binary zero
runs of length at most4. The two transport equations and B=65536D
therefore recover I<D and the upper initial digit1 by the established
free-height415 input argument. In particular D=1 is excluded after
this recovery. Each actual tile update is below B because its slope
plus offset is below65536. The same paid transports then recover positive
terminal digits below B and exact chronology. The free-height415 proof
now gives the same literal C2 word problem and universal accepted-input
conclusion. No old positive height-gap inverse is invoked.

## 4. Positive extensions and precise equivalence

For completeness, take any accepted input and its genuine finite tile
history. Choose the parent's sufficiently large dyadic D and exact packed
histories. Their unchanged lower blocks satisfy `H0 AND M0=Z` and (2).
The new q is dyadic and (3)–(4) make the new prescribed padded AND true.
The complete native converse supplies fresh strictly positive private
coordinates, including the same normalized strong treatment and paid
bound coordinate. For its canonical power X, `X/q>r` ensures the latter
is positive. Every canonical individual native unit is+1. Keep the
unchanged exponent52 extension and paid query, so both the merged and
separate complete polynomials vanish.

Conversely, Section3 reconstructs a genuine accepted history from every
new positive zero. One may explicitly recover an old415 extension:
use H0+BT and M0+(B−1)T, old scale16P^36, and fresh private native
witnesses. Dyadic B implies `B AND(B−1)=0`; the old ports fit even at
B=P. The native converse again supplies all positive private witnesses.
The outer histories and input/program parameters can be retained.
Thus the existential accepted-input projections coincide. This is not
an unchanged-coordinate or complete-polynomial identity.

## 5. Source replay and degree accounting

The receipt's off-zero audit executes the *old* source with four explicit
scalar-definition overrides: top mask2T, H=H0+2T, M=M0+T, and q=16BT.
It compares every retained register and every complete finalizer to the
new source on positive and signed assignments, including zero-selector
contexts. These checks verify the rewrite and declared scalar ports;
they do not imply arbitrary-point equality to the unmodified old source.

P still has degree2 and T degree68. The native scale's degree falls from
72 to69. The generic guarded degree propagation from the
[factor-partition packet](tseytin_universal_factor_partitions.md) verifies
the same two all-integer main-norm cancellations under the new source.
The word-factor bounds, in their retained order, are

    898,2080,485,69,1112,414,414,

with sum5472. The six exponent factors retain degrees5,7,14,22,3,3,
with sum54. All nonunit residuals have degree at most68. Thus the merged
anchored bound is5472+54+2*68=5662, and its SOS bound is2*(5472+54)=11052.
For separate units the corresponding bounds are5472+2*68=5608 and10944.
These are conservative upper bounds, not exact degree claims.

The audit includes120 positive global-sum source contexts(24 at D=1),
240 independent untyped extreme-port checks,341 binary top-split cases,
320 complete modified-port output identities(160 signed), and19 invalid
parent/successor rejections. All four schedules have full output closure.
The fixtures are component/source checks, not full native Pell zeros.
Author generation and fresh replay pass. Independent full proof/source/
dependency review and a separate fresh replay passed. The independent
executor checked384 complete register/manual-factor/finalizer/overridden-
parent identities(192 signed),16 zero-selector contexts, all four full
degree/opcode/closure ledgers,120 additional source pretyping contexts
(20 at D=1),5461 separate binary top splits and36 malformed successor
rejections. All seven local links and whitespace pass. Review clarified
an inherited narrative metadata field: the affine height identity belongs
to the historical415-to418 map, while this scale transfer rebuilds native
witnesses. No arithmetic or theorem changes were needed.
