# Bounded arithmetic search after the 90-operation binary product system

This note records one simpler Pell argument, three local arithmetic
obstacles, and a rejected 89-operation packing proposal. It changes no
published certificate and makes no improved operation-bound claim.
The reference system is `round37_1980_binary_product_certificate.py`:
48 multiplications and 42 additions, with fixed numerals and equality
tests free.

## 1. Direct decoding of the first exponential

The cube-growth hypothesis of the general exponent lemma is unnecessary
for this particular first exponential, once the exact main index and
the strict lower ratio have been established. Assume

    U,Y,r positive integers, J=2r+1,
    a=Y*(U+1), A=a+2, M=4a+3=4A-5,
    c=psi_A(J), d=chi_A(J),
    xi=(U+1)^(2r)/U^r<Y+1,
    d=U+a*c+gamma*M.                            (1)

For z_j=chi_A(j)-(A-2)psi_A(j), the Pell recurrence gives

    z_0=1, z_1=2, z_(j+2)=2A*z_(j+1)-z_j.

The sequence 2^j satisfies the same recurrence modulo M, because
4-4A+1=-M. Hence

    chi_A(J)-(A-2)psi_A(J)=2^J mod M.

Equation (1) therefore implies U=2^J mod M, without any division in
a residue ring.

For every U>=1, (U+1)^2/U>=4. Thus xi>=4^r, and integrality of Y
together with xi<Y+1 gives Y>=4^r. Consequently

    2^J=2*4^r<=2Y<=a<M,
    0<U<a<M.

Both representatives lie strictly between zero and M, so U=2^J as
integers. This argument works even if U has not previously been bounded
below by 4096.

The observation does not remove all uses of the definition U=w*n^2.
Earlier index-isolation arguments use lower bounds derived from U,Y,
and the definition also supplies the crucial divisibility making n a
power of two. The later binomial step needs n^2 dividing U. Merely
replacing U by a free positive input loses these implications. One may
weaken the defining divisor from n^2 to n and later recover n^2|U from
the size of 2^J, but that still costs one multiplication. No operation
saving follows from (1) alone.

## 2. Main reciprocal coordinates do not improve the shared count

Write D=A^2-1=a^2+M. Globally M,D,c^2 and U are already available:
D and c^2 remain needed in the relaxed and second Pell norms.
The first exponential and main norm currently cost seven operations:

    ac=a*c, D1=U+ac, G=gamma*M, d_calc=D1+G,
    d2=d*d, Dc2=D*c2, rhs=1+Dc2,
    d=d_calc, d2=rhs.

The positive reciprocal coordinate W=d-ac=U+gamma*M changes the
main norm into

    W*(W+2ac)=1+M*c^2.

Even allowing the old input d to be eliminated, the natural factored
schedule needs eight operations:

    G=gamma*M, W=U+G, ac=a*c, twice_ac=2*ac,
    Z=W+twice_ac, L=W*Z, Mc2=M*c2, rhs=1+Mc2.

The identity is exact, and positivity is harmless, but it loses one
operation. Counting the now-shared D calculation as deleted would be
incorrect: both later Pell blocks still consume D.

## 3. Two other positive-coordinate families

The half-parameter norm costs five operations once K and u are present:

    u2=u*u, y2=y*y, gap=u2-y2, L=K*gap, P=1-y2.

Its positive solutions have y>u. Replacing y by u+z with z>0 gives

    (K-1)*z*(2u+z)=u^2-1.

This needs seven operations: K-1, 2u, 2u+z, the two products on the
left, u^2, and u^2-1. The congruence block for u is unaffected. It
loses two operations.

For the first norm, put E=UY and Q=UY^2. Its present form

    tau*(tau+1)=(E^2+U)*(Yk)^2

costs six operations after E and the shared interval product Yk.
The odd-index half-factorization permits

    k=zv, tau=Qz^2, (Q+1)v^2-Qz^2=1.

Evaluating Q*(z^2-v^2)=v^2-1 needs six operations, including the
previously absent Q=E*Y; k=zv costs a seventh. The interval still
requires its existing Yk product. This family loses one operation.
Neither calculation treats division or a reconstructed coordinate as
a free arithmetic instruction.

The separate square-input proposal F=f^2 is not repeated here. Its
large-index auxiliary obstruction is documented in
`EXPLORATION_PELL_AFTER_PRODUCT_BOUND.md` and its exact modular receipt.

## 4. A genuine one-operation arithmetic proposal with a full obstruction

A stronger-looking size definition would replace

    n=q^8, ell+sigma+alpha=q

by the single equation

    n=q^4*(S+alpha), alpha>0.                     (2)

The old q^8 multiplication and two positive-bound additions are
replaced by one addition and one multiplication. The q^2 and q^4
registers remain needed by packing. Thus this is a real saving of one
addition as an arithmetic proposal: 48 multiplications and 41
additions. It would leave 34 positive unknowns and 21 equations.

It even gives valid pre-Pell bounds without either code range. From
sigma=(e-ell)C^2>0, C=x+g>=2, one has e>ell. Geometry and the binary
affine radix give theta=B-2>b and theta<B<=q^2. The packed quantities
are

    S=g+q^2*(ell+e*q)+q^4*sigma,
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b).

Since 1+theta*lambda<q^2,

    0<Tplus<q^4*(1+theta*ell)<q^4*S<n,
    0<S<n.

Also n is divisible by q^4, which retains the power-of-two implication
from n to q. Canonically one could choose alpha so that S+alpha is
a sufficiently large power of two. These facts explain why (2) is
more than a formal count manipulation.

Nevertheless (2) is unsound for the current compiler. The common-shift
construction in `EXPLORATION_BINARY_PRODUCT_ONE_SIDED_BOUND.md` gives,
for the fixed index of an inconsistent circuit and every positive x,
positive coding values with

    ell=ell_c+m*q^2, e=e_c+m*q^2,
    sigma=(e-ell)C^2 unchanged,
    S & (Tplus-1)=0.

Every fixed-index congruence is retained. Preserve all of these coding
values, but choose a power of two W>max(S,Tplus) and put

    alpha=W-S>0, n=q^4*W.

Equation (2) now holds. The integers n and q are powers of two,
S,Tplus<n, and 3L<=B<=n. Recompute

    r=S*(n^2-n)+Tplus*(n^2-1).

The same binary nonintersection and bounded packing lemma give
n^2|binom(2r,r), with n^2-1<=r<2n^3. Both S and Tplus are even in
the published common-shift construction, so this new r is even.

The positive necessity construction in `BASE_TWO_PELL_90_PROOF.md`
therefore applies at the new n,r, with the same fixed L and index.
It supplies every Pell witness, including U=2^(2r+1), the positive
interval and exponent quotients, and the half-parameter auxiliaries.
No requirement n=q^8 is used in that extension once the stated power,
growth, divisibility, and parity hypotheses have been supplied.

Thus the same inconsistent index still admits every positive input.
This is a full positive-domain transfer of the counterexample, not
merely an auxiliary-subsystem objection. The proposed 89-operation
source is not a universal encoding of the intended represented set.

The standalone `explore_round37_flexible_n.py` verifies all 89 primitive
statements and all 21 complete source residuals, including the inherited
acyclic corrections. Its JSON receipt is explicitly labelled
`ARITHMETIC_PASS_BUT_REPRESENTATION_REFUTED`; it certifies no improved
representation bound and does not materialize the enormous Pell witnesses.

All conclusions here concern the stated bounded families. They are
not an optimality claim for 90 operations.
