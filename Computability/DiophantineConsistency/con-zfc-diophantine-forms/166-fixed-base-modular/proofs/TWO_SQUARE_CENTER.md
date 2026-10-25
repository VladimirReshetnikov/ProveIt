# A two-square completion for the free Pell center

## Statement

Let W>=2 and let q and M be positive odd integers such that every prime
dividing M divides q. Put n=q+1, so 2n is invertible modulo M, and let

    a0 = (n^2+1)/(2n) = 1 + q^2/(2n)  (mod M).

There exist a positive odd integer k and integers u,v such that, with

    L = X_(Wk)(W+1),       A = L^2+u^2+v^2,

we have A=a0 modulo M. Moreover A can be chosen arbitrarily large,
and Y_(Wk)(W+1)/W is an odd integer. Therefore the existing odd Pell
frame and the common-root congruence are simultaneously complete with
the two-square constructor

    A=L^2+u^2+v^2

in place of A=L^2+u^2+v^2+w(w+1). Soundness is unchanged: A>=L^2
still supplies the required positive lower bound. The new constructor
saves one unrestricted integer coordinate, with no additional row.

For M=1 the congruence is empty: take k=1 and any arbitrarily large
u. In the proof below assume M>1.

In the proposed modular numerator application, M=N*q^x, N=B^x, and
q=(BH)^x. Hence every prime of M divides q. B and q are odd by their
literal affine constructors. These hypotheses are available before
choosing the center in completeness.

## Finite algebra for the choice of frame

Put D=(W+1)^2-1 and work in the finite commutative ring

    S_M = (Z/MZ)[s]/(s^2-D).

The element e=(W+1)+s is a unit of norm one. Let the finite
multiplicative order of e^W be 2^r k with k odd. Choose this k.
Then g=e^(Wk) has order a power of two. Its two coefficients are
L=X_(Wk)(W+1) and Y=Y_(Wk)(W+1), modulo M.

Fix a prime power p^a exactly dividing M. The image of g in S_(p^a)
also has order a power of two. We claim:

    either L is not +1 or -1 modulo p,
    or L^2=1 modulo p^a.

To prove this, suppose L=epsilon modulo p, epsilon in {+1,-1}.
If D is nonzero modulo p, the norm relation L^2-DY^2=1 implies
Y=0 modulo p. If D=0 modulo p, then the image of s has square zero.
An element epsilon+Ys of power-of-two order must again have Y=0:
raising it to its power-of-two order gives a linear nilpotent term
whose coefficient is a unit modulo the odd prime p. Thus in both
cases g=epsilon modulo p in the complete quadratic ring.

The kernel of S_(p^a)^times -> S_p^times consists of elements 1+pz
and is a finite p-group. Its order is p^(2(a-1)). The element
epsilon*g lies in this kernel and has power-of-two order, so it is
the identity. Therefore g=epsilon modulo p^a, proving the claim.

The use of the full quadratic ring, including the case p divides D,
avoids any unproved separability or nonramification assumption.

## Why two squares suffice in every residue class needed here

Consider c=a0-L^2 modulo p^a.

If L is not +/-1 modulo p, then a0=1 modulo p and c is a unit.
If L is +/-1 modulo p, the preceding claim gives

    c = a0-1 = q^2/(2(q+1))  (mod p^a).

The denominator is a p-adic unit. Thus c is zero modulo p^a or
has the even valuation 2*v_p(q). In every case c is zero or has
even valuation.

Every unit modulo an odd prime power is a sum of two squares.
Over F_p, the sets of squares and of c minus squares both have
(p+1)/2 elements, so they intersect. For a nonzero c, at least
one coordinate of the resulting solution is nonzero. Its derivative
2u or 2v is invertible, permitting the usual one-coordinate lift
through p^2,p^3,...,p^a. If c has valuation 2b<a, represent its
unit part modulo p^(a-2b) and multiply both coordinates by p^b.
If c=0 modulo p^a, take both coordinates zero.

Consequently c=u_p^2+v_p^2 modulo each p^a. Applying CRT separately
to the u_p and v_p gives u,v modulo M. Then L^2+u^2+v^2=a0 modulo M.
Replacing u by u+jM preserves the congruence and makes A arbitrarily
large. All values retain A>=L^2.

## Preservation of the odd frame witness

The inherited frame uses

    L^2 - W^3(W+2)(2z+1)^2 = 1.

For the minimal index W, its standard completeness proof supplies
Y_W(W+1)/W odd. For an odd multiplier k, the Pell composition formula
gives

    Y_(Wk)(W+1) = Y_W(W+1) * Y_k(X_W(W+1)).

For every integer b and every odd k, Y_k(b) is odd. This follows
immediately from Y_0=0,Y_1=1,Y_(j+2)=2bY_(j+1)-Y_j modulo two.
Thus Y_(Wk)(W+1)/W remains odd. Its sign is positive for the selected
positive center and index, so it supplies an integer z in the frame.

For completeness, the base parity fact can also be proved directly.
If W is odd, W+1 is even and Y_W(W+1) is odd. Modulo W the Pell
recurrence gives Y_W(W+1)=0, hence its quotient by odd W is odd.
If W is even, write a=W+1, which is odd. The identity
Y_(2m)(a)=2X_m(a)Y_m(a), with X_m(a) odd, gives
v_2(Y_W(a))=v_2(W), since the odd-index ordinate is odd. Again the
quotient is odd. This proves the required fact without a choice
of representatives modulo a rational ring.

## Role in the full construction

This lemma changes only the completeness choice of the frame and the
number of free-center witnesses. The canonical Pell identities,
semantic-anchor cap, and exact power arguments depend on the center
being sufficiently large, not on which sufficiently large center in
the permitted common-root residue class was selected. Those inherited
completeness statements must still be checked when composing this lemma.

The term 2nA-n^2-1 is divisible by M exactly at the displayed residue
class a0. The lemma neither approximates that congruence nor changes
the logical meaning of modular numerator tests. No assertion that
every nonnegative integer is a sum of two squares is made.

This is an ordinary proof of a cofinal residue-class completion.
It is separate from the general three-square representation theorem
and does not assert a globally minimal number of center witnesses.
