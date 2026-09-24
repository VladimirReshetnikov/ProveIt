# Positive shifted words: the mask rejects a bounded negative interval

This extends the domain of the popcount mask in
`EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md`. It permits one global
offset for a packed word whose intended digits are one or three.
It does not establish individual field bounds, a complete Life torus
system, or a new universal operation count. The earlier mask files
remain unchanged.

## 1. A negative-input exclusion for an arbitrary binary mask

Let L=2^b with b>=1, and let 0<M<L. For an integer P define

    r=(L-P)(L-1)+M,
    T=b+popcount(M).

For every -M<=P<0,

    popcount(r)<=T-1.                                  (1)

To prove this, write P=-s with 1<=s<=M, and set
a=s-1 and z=M-s. Then a,z>=0, a+z=M-1<L, and

    r=L^2+aL+z,
    popcount(r)=1+popcount(a)+popcount(z).               (2)

Both lower base-L digits lie below L. Let d=v2(M). The lowest d
bits of M-1 are all one. In the addition a+z=M-1, no carry can
start in these positions: the initial incoming carry is zero, and
a required output bit one with incoming zero has input sum exactly
one. Induction keeps the outgoing carry zero throughout these d
positions. There is also no carry leaving the highest position,
since a+z<L. At most b-1-d carry events remain possible.

If c is the total number of these events, the usual popcount identity
gives

    popcount(a)+popcount(z)=popcount(M-1)+c,
    popcount(M-1)=popcount(M)-1+d,
    0<=c<=b-1-d.

Substitution in (2) yields (1). The proof includes d=0 and M=1;
it makes no periodic-mask assumption and no assumption about the
digits of s.

The nonnegative part of the earlier mask proof is equally general:
for 0<=P<L, its two overflow branches give

    popcount(r)<=T,
    popcount(r)=T iff P AND M=0.

At the other endpoint, P=L gives r=M and popcount(r)=T-b<T.
Combining the statements proves

    for -M<=P<=L,
    2^T divides binom(2r,r)
       iff 0<=P<L and P AND M=0.                       (3)

Here r is positive throughout this displayed domain. This uses the
exact identity v2(binom(2r,r))=popcount(r). No claim is made for
arbitrary P<-M, where the argument no longer supplies nonnegative
lower base-L digits.

## 2. One global offset for positive words in radix 128

Let q>=4 and supply positive lambda and a positive packed integer
Pprime with

    L=q^7, 127*lambda+1=L,
    P=Pprime-lambda, M=125*lambda,
    r=(L-P)*(127*lambda)+M, D0=q^13.                    (4)

The quantity P is a signed computed register. Positivity gives
P> -lambda>=-M. Positivity of r also gives P<=L: if P>=L+1,

    r<=-(L-1)+M=-2*lambda<0.

In particular the complete preliminary domain is

    -lambda<P<=L.                                     (5)

The possibility P=L is retained in the preliminary proof. The mask
will exclude it after the Pell/binomial conclusion, rather than
assuming P<L in order to obtain that conclusion.

The same inequalities give

    M<=r<(L+lambda)(L-1)+M<2L^2.                       (6)

For the last inequality, lambda<(L/127) and M<L suffice; indeed
(L+lambda)(L-1)+M<(L+lambda)L<=128L^2/127<2L^2.
Also M=125(L-1)/127>L/2 for L>=4. With proof-only n=q^6,

    n<q^7/2<M<=r<2q^14<2n^3,
    D0=q^13>n^2,
    U,Y>=D0>n^2>=4096.

The strict n<q^7/2 uses q>=4. The retained kernel therefore has
E=UY>=q^26>r+1, a=Y(U+1)>q^26>2r+1 and
4r/a<8/q^12<1/2. These bounds establish the exact-index, ratio
and exponential hypotheses before a power-of-two or digit claim.
As in the nonsquare-scale audit in the general-mask note, the kernel
uses only the supplied scale in U=wD0,Y=sD0 and concludes

    U=2^(2r+1), D0 divides binom(2r,r).

Consequently q=2^e for some e>=2. Now L=128^e, the radix digit
count is N=e, and

    popcount(M)=6N, log2(L)=7N,
    2^T=2^(13N)=q^13=D0.

Applying (3) on the domain (5) excludes every negative P and the
endpoint P=L. It proves that P has radix-128 digits zero or two.
Because lambda has every digit one, addition has no carries, so

    Pprime=P+lambda has exactly N digits, each one or three.  (7)

Conversely, if Pprime has those N digits, then P=Pprime-lambda
has digits zero or two and is nonnegative. Equation (3) supplies
central-binomial divisibility. Since M is odd and P is even,
r is odd. The 43-operation odd-index sign variant in
`EXPLORATION_ODD_INDEX_PELL_SIGNS.md` supplies all positive canonical
Pell witnesses. In particular D0 is now a power of two, and
D0<r^2<U=2^(2r+1), because r>=M>L/2 and q>=4. Thus U/D0
is positive integral; rounding gives the same assertion for Y/D0.
The remaining witnesses are those of the existing positive
construction. The global subtraction P=Pprime-lambda costs one
operation and does not require a separate nonnegativity witness.

## 3. What follows for concatenated positive planes

If q is a power of 128 and there are seven fields with proved
individual bounds 0<Fi<q, write

    Pprime=F0+qF1+...+q^6F6,
    Jfield=(q-1)/127.

There is no overlap between their base-q positions. Under these
bounds, (7) is equivalent to saying that every radix-128 digit of
every Fi is one or three. Therefore

    Fi=Jfield+2*Bi,

where Bi is a Boolean radix-128 word of the field length. Such Fi
are always positive, including when Bi is the zero word. This is a
mathematical witness map; the subtraction and division for each
individual Bi need not be constructed if all local equations and
alignment are written natively in Fi.

The independent field bounds cannot be inferred from the packed
mask. Here is an exact alias with q=128 and one digit per field.
The canonical field list

    (1,3,1,1,1,1,1)

and the positive but invalid list

    (129,2,1,1,1,1,1)

have the same packed integer. In both cases Pprime=lambda+2q,
so P=2q passes the mask. In the second list F0>=q and F1 has a
forbidden digit. This is a counterexample to deducing individual
field validity from positivity and the single packed mask alone.
It is not asserted to satisfy additional Life or torus equations.
Structural range recovery or explicit field bounds remain required.

## 4. The precise local Life offset and its unshared cost

For the homogeneous local relation

    N+22Y+6(U1+U2-B)+7U3=11U4+14U5,

replace each Boolean plane by its native positive word Jfield+2F.
The sum of eight neighbors contributes 8Jfield. The full constant
on the left minus that on the right is

    (8+22+6+7-11-14)*Jfield=18*Jfield.

Thus the same left and right expressions in the positive native
words satisfy

    lhs=rhs+18*Jfield.                                (8)

The inclusive nine-neighbor formulation has the same offset:
9+22+12+0-11-14=18. This calculation accounts for all shifted
center, target and auxiliary fields, rather than only the masked
auxiliaries. The nonnegative side bounds and exact local equivalence
follow by substituting Fi=Jfield+2Bi and cancelling this offset.
The carry-free bounds apply after that affine cancellation; the
larger uncancelled native sides can themselves contain carries.

If Jfield is not otherwise available, 127*Jfield+1=q uses one
multiplication and one addition. Directly adding the correction
in (8) uses one multiplication by 18 and one addition to rhs.
Together with the global packed subtraction, these are five
specified additional operations. This is only an accounting of
that explicit adaptation; it neither proves an optimal cost nor
counts the field concatenation, torus alignment, target encoding,
field bounds, or the full Life system.

## 5. Exact finite corroboration

`../verification/explore_positive_shifted_boolean_mask.py` checks
the negative exclusion for arbitrary masks in complete bounded
binary lengths, including the trailing-one carry bound. It checks
the whole shifted-word predicate in a complete radix-128 sample,
pre-power bootstrap inequalities at admissible powers and non-powers
of two, the concatenation alias, and all finite Life local offset
identities. Its JSON receipt separates those checks. It does not
instantiate a complete large Pell witness or assert a universal bound.
