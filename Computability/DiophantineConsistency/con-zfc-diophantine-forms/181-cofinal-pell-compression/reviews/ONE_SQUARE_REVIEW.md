# Independent mathematical review: one-square cofinal Pell centers

Reviewed for the current ProveIt research iteration on 25 October 2026.
This is an independent AI-assisted mathematical review, not external human
peer review or a proof-assistant certificate.

## Verdict and exact scope

The proposed theorem is correct under its stated premises: W is an even
integer at least two; q and M are positive odd integers; every prime divisor
of M divides q. With n=q+1 and a0=(n^2+1)/(2n) modulo M, there exist an odd
positive k and an integer u such that

    L = X_(Wk)(W+1),  A = L^2 + 2u^2 = a0 (mod M).

The center A can be arbitrarily large, and Y_(Wk)(W+1)/W is an odd positive
integer. This replaces the two-square constructor in package166 by one
weighted square after making the magnitude frame even.

The source files reviewed were package166's `proofs/TWO_SQUARE_CENTER.md`,
`proofs/FRAME_AND_AFFINE_PROOF.md`, and `code/build_frame_compressed.py`, at
ProveIt commit 02a78a08603cbae248c19c23a75907c6c6bd6443. The new theorem was
checked independently from the proposed proof, including the ramified
quadratic-ring case and the exact power-of-two order argument.

## Independent proof audit

Put D=W(W+2), and let e=(W+1)+s in
S_M=(Z/MZ)[s]/(s^2-D). Its norm is one. Let the multiplicative order of e^W
be 2^r k with k odd. Then g=e^(Wk) has power-of-two order. Write its
coordinates modulo M as L,Y.

For each p^a exactly dividing M, first consider L=epsilon modulo p with
epsilon=1 or -1. If D is nonzero modulo p, norm one implies Y=0 modulo p.
If D=0, an element epsilon+Ys of power-of-two order in the dual-number
ring has Y=0 as well: a nonzero nilpotent part would survive raising to
every power of two, since p is odd. Thus g=epsilon modulo p. The reduction
kernel from the quadratic algebra modulo p^a to modulo p is a p-group.
The element epsilon*g belongs to that kernel and has power-of-two order,
so it is one. Therefore L^2=1 modulo p^a.

In that case

    (a0-L^2)/2 = q^2/[4(q+1)] (mod p^a).

The unit q+1 is 1 modulo p and has a square root modulo every p^a by
one-coordinate Hensel lifting from 1. Hence the displayed residue is a
square, including when q^2 vanishes modulo p^a. No cancellation by a
possibly nonunit q is used.

Now consider L not equal to either 1 or -1 modulo p. The norm equation
implies D and Y are nonzero modulo p. The element g has order at least four,
because the only norm-one elements of order dividing two are scalar 1 and
-1. Since W is even and k is odd, the order of e modulo p is divisible by
eight. Choose a power h=H+Zs of e with exact order eight.

Here is the short algebraic square certificate, avoiding quadratic
reciprocity or a formula for the order of the norm-one group. The only
nontrivial norm-one involution is -1, so h^4=-1. Consequently
conjugate(h^2)=h^(-2)=-h^2, and the scalar coefficient of h^2 vanishes.
Combining H^2+DZ^2=0 with H^2-DZ^2=1 gives

    H^2=1/2,  DZ^2=-1/2,  (DZ)^2=-D/2.

Since a0=1 modulo p, we obtain the nonzero square

    (a0-L^2)/2 = -DY^2/2 = (DZY)^2 (mod p).

The nonzero root lifts to every p^a, because the derivative of u^2-c is
2u and p is odd. CRT combines the local roots. Replacing u by u+jM preserves
the congruence and makes L^2+2u^2 arbitrarily large. The case M=1 is immediate.

For parity, D is divisible by 2W since W is even. The binomial formula for
e^(Wk) modulo 2W gives

    Y_(Wk)(W+1) = Wk*(W+1)^(Wk-1) = W (mod 2W).

The last equality uses k odd, W even and (W+1)^2=1 modulo 2W. This proves
both W-divisibility and oddness of the quotient directly. Positivity follows
from the positive base and positive index.

As an independent cross-check of the order-eight step: the norm-one group
over F_p has order p-chi(D). Its divisibility by eight forces p=1 mod8
when D is a square and p=7 mod8 otherwise. The quadratic-character identity
chi(-D/2)=1 follows in both cases. The main proof does not require this
alternative argument.

## Source-level composition

The package166 magnitude frame is W=2+sum a_i^2. Replacing this with
W=2+2sum a_i^2 forces W even using the same coordinate and retains all
of the source's required bounds. In particular W>=t^2+2, each retained
atom is bounded in absolute value by W, and the omitted radius satisfies
R^2<=2((R+t)^2+t^2)<=W-2<W^2. The new inequality is at least as strong
as the source's original estimate. The center still obeys A>=L^2.

The source completeness construction chooses its semantic quantities before
the frame and chooses the center afterward. Thus changing the computed
frame does not create a dependency cycle. The odd-multiple frame choice and
arbitrarily large center preserve the required cofinal choices.

This is an existential semantic reduction, not a polynomial bijection from
every old center assignment to a new one. A checker must not advertise
the altered two rows as an invertible algebraic identity. Subsequent
coordinate and residual operations can still be certified exactly, using
their actual changed inputs. Counts after such operations must be measured
from the final emitted equations rather than obtained by subtraction.

## Finite controls

`check_one_square_independent.py` enumerates finite quadratic-ring orders
directly and independently enumerates square residues. It checks 408 even
frames and 2040 center residue instances; 164 frames are ramified at some
prime of the modulus. All pass, including the odd quotient condition.

The script also tests an actual obstruction to deleting the evenness premise:
W=3, q=M=19. The order of e^W modulo 19 is 20, and every odd multiplier k
modulo 40 fails the required one-square center congruence. This demonstrates
that the parity hypothesis has mathematical content.

These finite checks are regression controls. The unbounded proof above is
what establishes the theorem. Logical calibration to syntactic ZFC refutations
remains the identified inherited dependency; this review does not rerun it.

## Preferred refinement: change only the frame constant

A later refinement is also correct and preferable for package166: use

    W=3+sum a_i^2

in place of W=2+sum a_i^2, leaving the coefficients of all square atoms
unchanged. Evenness is required for the newly constructed completeness
witnesses only. Soundness of an arbitrary new source zero uses A>=L^2
and the inherited frame lower bounds, all of which remain valid.

Section10 of `MODULAR_PROOF.md` explicitly chooses even x, odd actual a,
eight other even actual CRT representatives, even derived J, and odd B and
H. Its later congruence adjustments preserve every one of these parities.
The 21 frame atoms are t, x, y+1, R+t, B; the nine actual representatives;
and N, J, q, D_t, D_y, M, BH. Since R=16^t is even, the pair t^2+(R+t)^2
is even regardless of the parity of t. The x and J squares are even.
The eight odd atoms y+1,B,N,q,D_t,D_y,M,BH contribute an even sum. The nine
representatives contribute an odd sum. Hence the entire sum of 21 squares
is odd, and adding three makes the canonical W even.

This argument does not impose any extra global restriction on the solutions
of the polynomial. It chooses suitable canonical completeness witnesses,
as the inherited construction already does. The raw frame constant changes
from -525 to -526 after the source's translated affine atoms are expanded.
The preferred refinement therefore adds no coordinate or residual, and only
changes that constant in the frame row before the center-coordinate deletion.
