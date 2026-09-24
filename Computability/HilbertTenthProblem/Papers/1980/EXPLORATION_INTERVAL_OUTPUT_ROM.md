# Direct dense-gap output does not fit the existing fixed-row ROM

The top-mask gap is gD, where g=(R-3)/6. One might make the program
emit this interval word directly instead of emitting the head word D,
and thereby remove its separate typed zero/complement pair. The direct
substitution has an attractive formal arithmetic ledger, but it fails
the existing ROM's row bounds and rejects its canonical histories.
This note establishes that scoped obstruction; it does not rule out
a different encoding of interval outputs or give a new universal count.

## 1. The fully charged tentative replacement

Start from the complemented-guard104 architecture, with positive
gap parameter t and top source6t=(R-3)D. Decompose its fixed program
table into Kbase+Kzero, where Kzero contains exactly the complementary
zero-output terms

    Kzero=sum_(i emits nozero) 3^(d+bz-a_i).

Introduce a positive g with6g=R-3 and use the variable table

    K(R)=Kbase+gKzero.

Replace the projected output hzD by hzt. In an honest interpretation
t=gD. Remove both zero-head masks and instead mask t itself. The
eleven fields would be

    Kp, t-A0, A0, t-A1, A1, Km, t, C, V, TC, TV.

This does not declare K(R) a free numeral: its product gKzero and
addition to Kbase are charged. The fixed Kbase and Kzero may be free
numerals, as elsewhere.

The former top source has two products6t and(R-3)D, plus the already
computed R-3; the former Z+D=H costs one addition. The new6g relation
uses one product and the same R-3. Constructing K(R) costs one product
and one addition, exactly cancelling those savings. Projecting hzt
still costs one product, as did hzD.

Removing one net field saves a Horner product and addition. The new
eleven-field scale q11 requires five products rather than the old four:

    q2, q4, q8, q10=q8*q2, q11=q10*q.

Thus this exact local ledger would be104-2+1=103, or55M+48A. It is
**not a certificate for a correct system**: the changed table and its
mask support fail the proof obligations below. Additional alignment
conditions or wider program frames would have to be specified and
charged before making any operation claim.

For a hypothetical honest converse, choosing an odd ternary width m
would make g=(3^(m-1)-1)/2 even, so insertion of gD in place of the
two even-sum head fields need not itself impose an extra parity
operation. This observation does not repair the row obstruction.

## 2. No increase of R repairs the old row bound

The old table's zero labels occupy fixed monomial positions. Let
hz=3^(d+bz). If state i emits nozero, Kzero contains
3^(d+bz-a_i), so Kzero*3^a_i contains hz. Therefore

    g*Kzero*S >= g*hz.

For every R>=9, g=(R-3)/6>=R/9. The fixed hz is at least9. Thus

    K(R)S >= g*Kzero*S >= R.

Consequently the usual strict row-product bound K(R)S<R is impossible
for every width. It is not repaired by taking a larger permitted
power of three. The interval g has m-1 consecutive ternary one digits,
so shifting it by a fixed positive label exponent necessarily spreads
it past the end of an m-digit row.

This failure alone is an obstruction to reusing the old proof, not a
logical impossibility theorem for all global carry treatments. The
next argument shows that the unchanged canonical transformation
actually fails its packed bound, rather than merely lacking that
particular row estimate.

## 3. Cross intervals force canonical junk beyond the whole word

Consider a chosen edge i->j. Its proposed row junk is

    V_i=(Kbase+gKzero)3^a_i-gmarker*3^a_j
         -hs*sign_i-hz*g*nozero_i
       =Vbase_i+g*(Kzero*3^a_i-hz*nozero_i).

Here gmarker=3^d is the unchanged fixed marker numeral; it is distinct
from the variable interval factor g. The base junk is nonnegative,
because the chosen edge and sign terms are explicitly in Kbase.

For any other nozero-emitting state k!=i, the remaining cross part
contains the positive monomial

    3^e, e=d+bz+a_i-a_k.

The fixed coordinate construction makes e>=2. Hence V_i>=g*3^e>=R.
Multiplication by the interval factor cannot cancel this term: the
subtracted own-state output was removed before the cross part was
multiplied, and all remaining terms are nonnegative.

The current six-state program has five nozero-emitting states, so
every active row has such another emitter. In particular its last
source row has V_last>=R. Every earlier row has nonnegative junk,
therefore a u-row canonical history has

    V=sum_i V_i R^i >= R*R^(u-1)=q.

The unchanged test word TV=V+ZstarH is then greater than J=(q-1)/2.
But the positive eleven-field raw packing, shared native offset and
bound r<q11 require TV<=J. Thus the direct transformed canonical
history is rejected by its actual packed bound. The routing identity
itself still holds exactly; the failed conditions are the required
range and mask interface.

This argument also illustrates why fixed Sidon spacings alone do not
isolate the new outputs. Multiplication by g turns each single
cross-junk bit into an interval almost as long as the variable row.
Those intervals overlap label regions and later rows. A new mechanism
would need to handle that overlap explicitly, rather than inheriting
the single-bit ROM decoder or treating a variable table as free.

## 4. Exact checks and scope

`../verification/explore_interval_output_rom.py/.json` reconstructs the
table split from the unchanged published six-state program. It checks
the exact row-junk decomposition for every edge at three successive
widths and verifies the uniform lower bound V_i>=R. It then directly
transforms the complete canonical x=1 and x=2 paths and checks both
the exact global routing identity and V>=q, hence TV>J.

The103 ledger is reported explicitly as formal and invalid for this
unchanged encoding. No published104 source, proof or receipt is
modified. Possible wider-frame controllers, cancellation encodings or
different interval masks remain outside this scoped negative result.
