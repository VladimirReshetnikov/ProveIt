# Recover the factorial output sign after the first two power requests

This is a separate ordinary guard-redundancy proposal for the exact principal
Round15 source in `125-unified-binomial-round15/direct/unified_reparam_derived_shell/`.
It changes neither a natural-source generator nor any power, frame, remainder,
factorization or refutation interface. No new projected size is claimed here.
The actual source bindings and both integer witness maps must be checked before
this proposal licenses a materialized endpoint.

Let F denote `fact0.output`, B denote `choose0.output`, q denote `pow2.output`,
t=t0+16, V denote `pow0.output`, and L denote `pow4.output` in the actual
source. Keep all existing source rows and all 38 guard predicates except
the single scalar predicate F>=0. In particular retain the two factorial
remainder predicates u>=0, s>=0, the output slack o>=0, the first substituted
remainder anchor a>=0,b>=0, and the t-index slack. All variables are integers.

The bootstrap uses only the t-indexed requests until F's sign is recovered.
The original proof's simultaneous positivity of every seed exponent must
therefore be delayed; it cannot be assumed at the start of this argument.

The literal remainder rows give

    B=u+s+1>=1,
    q=B+o+1>=2,
    L=q*a+b+2>=2.

These bounds use no sign of F and no intended value of a power or binomial.
The t0 predicate gives t>=16. The retained t-index slack gives its actual
main Pell ordinate Y_t>=t>=1.

The common square frame W=2(2+sum of the actual requested atoms squared)
is positive and bounds the absolute values of every requested base, exponent
and output, including the possibly signed F-dependent atoms. The retained
frame signs and norm imply A>W^W. The retained common ordinate predicate
Vaux>=1 and its product-of-squared-ordinates identity show that every seed
ordinate is nonzero and that Y_t^2 divides Vaux. The common norm and comparison
base construction are independent of F's sign and of the signs of the other
seed exponents. In particular the common comparison base is at least five,
with the same two exact congruences as in the original proof.

Apply the original indexed-Pell argument solely to the t pair. It uses
t>=1, Y_t>=t, Y_t^2|Vaux, the common norm, and the two actual t-pair congruences.
It yields Y_t=psi_A(t)>0 and X_t=+/-chi_A(t). The request with base q>=2
and output L>=2 excludes the negative abscissa: under the strict frame
bound that branch would imply L*q^t=-1. Hence the pair is positively
oriented and L=q^t. No K-indexed or other F-dependent request has been used.

The other request attached to this SAME positively oriented t pair has
base F^2+1, which is at least one for every signed integer F. The original
small-residue argument now gives

    V=(F^2+1)^t>=1.

There is no base-one sign ambiguity because the pair was already oriented
using q. The frame bounds this actual base and output before interpreting
them, so the usual strict modulus bound applies also when F is negative.

Subtracting the two literal factorial rows, and using the literal gate
for F*B, gives

    F*B=V+s>=1.

Since B>=1, this forces the integer F>=1. This is precisely the omitted
sign, recovered before it is needed for any remaining exponent. The endpoint
row next gives y=F+r0+1>=1. All former monotone seed bounds, including
K=2R>0 and the derived label exponent, can now be established in their
original order. The original proof can resume from this point. In fact
resuming its full source equivalence is unnecessary for the local theorem:
F>=0 already permits restoration of the deleted guard witness directly.

The two witness directions fix the entire non-guard body tuple. From an
old guarded zero, discard the F guard triple. Conversely, a zero with the
other guards still present satisfies F>=1 by the preceding argument.
Choose integers alpha,beta,gamma with

    F=alpha^2+beta^2+gamma*(gamma+1),

using the same Legendre representation theorem as the original compiler.
The deleted triple occurs only in its own guard row, so filling this row
does not change any other residual. This proves equivalence after
existentially quantifying the guard witnesses. It is not a bijection of
whole guarded tuples and does not prescribe a polynomial choice of the
three witnesses.

The remaining finite obligations are exact source and guard bindings,
the privacy of the deleted triple, and explicit binding of every partial
t-index/frame/power premise above to the actual source. Any later monic
projection and centering need their own complete inverse and coefficient
checks. There is no claimed variable-count gain before those artifacts
are materialized. All inherited C222/Pell/refutation calibration remains
explicit; no new Lean endpoint, consistency proof or optimum is asserted.
