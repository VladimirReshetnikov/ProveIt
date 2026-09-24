# Dropping ell from the product bound admits a bounded repair of a false row

The published 91-operation construction uses

    sigma=(e-ell)C^2>0, ell+sigma+alpha=q.

Replacing the bound by sigma+alpha=q would save one addition. The
following construction explains why that replacement does not preserve
the represented set. It concerns this particular change to the current
compiler and packing. The published system and proof are unchanged.

## A compiler with one false pair

Use the fixed-index compiler in PRODUCT_BOUND_91_PROOF.md. Compile the
empty system of solutions given by the equation 1=0, retaining all its
input helpers and normalization rows. The final zero constraint can be
written as 2 delta delta_copy=0, with delta_copy a fresh copy of delta.
For every positive input x, assign the helpers and normalizations their
usual values, including delta=delta_copy=1. All ordinary rows are true
except the two signs of this final constraint. Their raw target values
are +2 and -2. Let t be the target of the negative row. Its next two
positions are empty, and its incoming signed carry is zero.

Choose the power-of-two radix B arbitrarily large after fixing the
physical values. In particular, take B>=4H0, B>H0+1+x, all raw
coefficients smaller in absolute value than B/4, and 7x^2<B/4. Put

    b=B-H0-1, theta=B-4, q=B^L, n=q^8,
    lambda=(q^2-1)/(B-1),
    C=C(B), g=C-x, ell_c=ell0(B), e_c=e0(B),
    Omega=D(B)=e_c-ell_c, sigma=Omega*C^2.

The superscript-free D here is the coefficient polynomial. All codes
are the actual finite compiler codes. Their degrees give

    ell_c,e_c<B^K, C^2<B^(2K), 0<sigma<q,
    L>3K+2.

Enlarging B ensures the last strict bound as in the published necessity
proof. The new weakened bound is satisfied by alpha=q-sigma>0.
The first and middle canonical masks pass. Every canonical third mask
passes except the negative row: its first three digits represent -2
modulo B^3. The positive row +2 is permitted by the digit bound three.

## A short correction and the fixed-index congruence

Define

    m0=(B+2)B^t.

Adding m0 to the effective third coordinate changes its negative row
from -2 to B, whose tested digits are (0,1,0). No other tested window
changes. The target spacing and the signed-reset proof guarantee that
the addition introduces no carry into another window.

We must also preserve the fixed-index congruence. Write

    theta=4r0, r0=B/4-1,

where r0 is odd and coprime to B. Choose 0<=k<r0 such that

    m=m0+kB^(K+1) == 0 mod r0.

The inverse of B^(K+1) modulo r0 exists. This adjustment lies above
every tested position. Since 4 divides q^2, it follows that

    theta | m q^2(q+1).

The degree and coefficient bounds give

    0<m<B^(K+3), mb<B^(K+4)<q, theta*m<q.

In particular m is much smaller than q, and B divides m. Set the
supplied codes to

    ell=ell_c+m q^2, e=e_c+m q^2.

Their difference is still Omega, so the exact positive product and
weakened bound are unchanged. The middle source expression is

    S2=ell+eq=(ell_c+e_c q)+m q^2(q+1).

Its fixed congruence remains true, with a strictly larger positive
quotient. Both supplied codes are now larger than q; the discarded ell
term in the bound was what excluded this common shift.

## The normalized packed masks

Write S2_c=ell_c+e_c q. The packed input is exactly

    S=g+q^2 S2_c+q^4 (sigma+m(q+1)).

The first two displayed coordinates remain below q^2. The third one
is also below q^2 after the chosen degree bounds: sigma<q and
m<B^(K+3)<=q/B^2. In particular all coordinates fit their original
q^2,q^2,q^4 widths.

For T=Tplus-1, the exact corresponding expansion is

    T=(q^2-1-b*ell_c)
      +q^2(theta*lambda-mb)
      +q^4(theta*ell_c+q^2*theta*m).

The first block is the original positive mask. The middle block is
positive and below q^2. The last block is below q^4 because
theta*ell_c<q and theta*m<q. Thus this is also a genuine block
decomposition, with no borrow between its displayed blocks.

The first mask is unchanged. For the middle mask, the only altered
positions below K are t and t+1, because the high adjustment begins
at K+1. The exact two digits of (B+2)b are

    B-2H0-2, B-H0.

Subtracting them from the usual mask digit B-4 gives

    2H0-2, H0-4.

Both are nonnegative even integers below B. The canonical ell digits
at these two positions are one, so their binary intersections are
zero. All other nonzero ell digits see their old mask. The high
adjustment contributes kb B^(K+1), where k<B/4 gives kb<B^2/4.
Its subtraction can cause a local low-digit borrow, but that borrow
clears in the next mask digit B-4: the upper digit of kb is below B/4.
Thus only positions K+1,K+2 are changed there, all below L and above
the support of ell_c. The e_c block above position L also sees its
unchanged mask. Hence
the entire middle coordinate S2_c passes.

The last mask is theta*ell_c+q^2*theta*m. The second term begins at
position 2L, whereas the effective third coordinate is below q^2;
their intersection is zero. The first term is supported below K.
At those low positions the effective third coordinate agrees with
sigma+m0: the m*q term starts at L, and the k adjustment starts above K.
Every low indicator test therefore passes, including the repaired
false row with digits (0,1,0). All three packed binary masks hold.

## Bounded packing and the positive Pell extension

The displayed block bounds give 0<S,Tplus<n=q^8. Consequently

    n^2-1<=r=S(n^2-n)+Tplus(n^2-1)<2n^3.

The original binary packing lemma applies to the normalized coordinates
and gives the required central-binomial divisibility. Moreover, B
divides g and the new ell. The formulas for S and Tplus imply that r
is even, so J=2r+1 is one modulo four.

The positive Pell necessity construction depends on these powers,
binomial divisibility, growth bounds, and this parity; it does not
depend on canonicality of the supplied ell and e. Therefore all its
positive main, first-index, second-index and half-parameter auxiliary
witnesses can be supplied exactly as in PRODUCT_BOUND_91_PROOF.md,
Section 5. The changed coding witnesses have already been constructed:
alpha=q-sigma>0, e-ell=D(B)>0, the positive fixed-congruence quotient,
and all original input/support witnesses. No supplied Omega is needed.

Thus this fixed index for the inconsistent equation 1=0 admits every
positive input after the proposed one-addition bound replacement.
This is a bounded-packing counterexample, not an argument based merely
on allowing the packed integer r to grow without limit.

## Exact finite corroboration and scope

The script explore_product_one_sided_bound.py reuses the complete
35-coordinate sample helper compiler and its exact coefficient checks.
It assigns its zero-constrained coordinate the value one, so precisely
one ordinary pair is false with raw values +2,-2. In four cases it
checks the original rejection, all 418 repaired indicator positions,
the exact two changed middle-mask digits, and the fixed-congruence
adjustment by modular arithmetic with the actual large support exponents.

This finite sample verifies false-row acceptance, not nonmembership
in that particular sample's represented set; that set has other valid
assignments. The empty-set circuit above is the general nonmembership
argument. The script does not instantiate the full universal Pell
witnesses or replace the positive-extension proof. Independent review
of the complete note and an independent rerun of all four sparse
checks pass, including the bounded packing and positive extension.
