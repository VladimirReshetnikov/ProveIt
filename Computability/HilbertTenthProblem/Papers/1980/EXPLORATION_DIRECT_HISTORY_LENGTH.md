# An 81-operation finite history system with a direct length parameter

**This is an exact improvement of the finite moving-frame history
relation, not a universal certificate below 90.** The system has positive
parameters I,F, 30 positive unknowns, and 20 equations. Its certificate
uses 81 arithmetic operations: 44 multiplications and 37 additions or
subtractions. Fixed numerals and equality tests are free.

The complete primitive schedule, fresh source polynomials, and exact
residual comparisons are in
`../verification/round43_1980_direct_history_length.py` and its JSON
receipt. An independent read and invocation of `verify_certificate()`
reproduced those counts and all 20 source checks, including the
triangular auxiliary correction and the symbolic forward witness map.

## 1. The single arithmetic change

Start with the 82-operation system in
`EXPLORATION_IMPLICIT_BOUND_MOVING_FRAME.md`. Previously its supplied
coordinate q was the square root of the complete tableau length Q.
Supply Q itself as q instead. Thus the new abbreviations are

    Q=q, W=v^2, L=Q^8, D0=Q^12,
    T=B+hrow,
    P=D+Q*X+Q^2*E+Q^3*Z+Q^7*T.                    (1)

Keep the same 13 positive outer unknowns

    q,v,quot,hrow,B,C,Y,D,X,E,Z,alphaI,lambda

and the same 17 positive Pell unknowns

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

The ten outer equations are

    q=v*quot,
    Q-1=hrow*(W-1),
    B=4C,
    B+C=X+2D,
    4B+D=Z+2E,
    Y+E=X+D,
    I+alphaI=v,
    I+W*Y=C+Q*F,
    3lambda+1=L,
    r=(L-P)*3lambda+2lambda.                      (2)

The other ten equations are exactly the retained Pell equations of
the predecessor, with U=wD0 and Ypell=sD0. Equivalently, they are
equations (K) of `EXPLORATION_RULE110_FIXED_INPUT_BOUND.md` with the
new squared scale D0=q^12. Their 43-operation schedule is unchanged;
its proof interface is the first-index, first-exponential, and
rounding argument in Sections 1-6 of `BASE_TWO_PELL_90_PROOF.md`.

Delete the primitive Q=q*q and replace every use of that register
with the supplied q. The shared power chain becomes

    Q2=q*q, Q4=Q2*Q2, L=Q4*Q4, D0=L*Q4.           (3)

These four multiplications compute q^2,q^4,q^8,q^12. Every other
primitive and equality is retained. The outer schedule therefore
has 38 operations, and the unchanged Pell schedule has 43, totaling
81. No witness or equation has been deleted. In particular, the
geometry equation q=v*quot remains part of the system.

## 2. Preliminary bounds do not require a square length

Consider an arbitrary positive integral solution. The input equation
gives v>=2. Since hrow>=1, the geometric equation gives

    Q-1=hrow*(v^2-1)>=v^2-1,
    Q>=W>=4.                                      (4)

This replaces the predecessor's deduction Q=q^2>=4. All subsequent
preliminary inequalities use Q as a positive integer at least four,
so they apply unchanged. For completeness, positivity of r and
3lambda=L-1 first gives P<=L. Since the other four packed terms
are positive,

    Q^7*T<P<=Q^8,
    0<B<T<Q.

The local equations imply

    D<5Q/8, X<5Q/4, E<37Q/16, Z<37Q/8.

Consequently the lower packed part satisfies

    0<R=D+QX+Q^2E+Q^3Z<(141/16)Q^4<Q^7.

It follows that T=floor(P/Q^7), and the integer T<Q gives P<L
strictly. With the integer N0=Q^6, these inequalities give

    N0<r<L^2=Q^16<N0^3, N0>=64.                  (5)

Only D0=N0^2 is a computed register. Equations (4)-(5) provide the
original retained-kernel hypotheses N0<=r<2N0^3 before any power
or Boolean conclusion. The proof does not import the obsolete
stronger lower bound N0^2<r.

## 3. Recover geometry before applying the Boolean mask

Apply the retained Pell argument in its established order. Its
first exponential and rounding conclusions are

    U=wQ^12=2^(2r+1),
    Q^12 divides binom(2r,r).                     (6)

Thus Q=q is a power of two. Write q=2^e. Because v divides q and
v>=2, write v=2^m with m>=1. The remaining geometric equation is

    2^(2m)-1 divides 2^e-1.                       (7)

This forces 2m to divide e. Indeed, write e=2mt+s with
0<=s<2m and reduce 2^e-1 modulo 2^(2m)-1. The remainder
2^s-1 is between zero and that divisor minus one, so (7) implies
s=0. Equation (4) also gives e>=2m. Hence t>=1 and

    W=4^m, Q=W^t, hrow=1+W+...+W^(t-1).          (8)

In particular Q is a power of four. This deduction now precedes
the periodic Boolean-mask lemma; it replaces the old immediate
conclusion from Q=q^2. The mask lemma of
`EXPLORATION_PERIODIC_DIGIT_MASK.md` therefore applies to (6),
P<L, and the final equation of (2), and proves that P is Boolean
in base four.

The rest of the implicit-bound proof has exactly its old hypotheses.
It extracts the Boolean fields T,D,X,E and the entire Z, including
Z's possible extra digit above Q. The fact that T=B+hrow is Boolean
excludes m=1, because then hrow is the largest Boolean word below Q
and T>hrow. Therefore m>=2 and I<v<=W/4. The same causal argument
recovers B Boolean, its zero first columns, and the exact moving-frame
Rule 110 trajectory. The final physical row 4F may extend one cell
beyond the packed source width, exactly as in the predecessor.

This order is noncircular: positivity first gives (4)-(5); Pell gives
(6); the retained divisibility equation gives (8); only then are the
mask and causal Boolean arguments used.

## 4. A bijection of all positive solutions

There is also an explicit equivalence with the complete predecessor
system, stronger than merely constructing canonical history witnesses.
Use subscripts old and new only on the two reparameterized coordinates.
Given any positive 82-operation solution, set

    q_new=q_old^2,
    quot_new=q_old*quot_old,                       (9)

and retain every other witness. All values Q,W,L,D0,P,U,Ypell and
all local and Pell coordinates are unchanged. The first source
residual becomes

    q_new-v*quot_new
      =q_old*(q_old-v*quot_old),

and each of the other 19 fresh source residuals equals its old
counterpart exactly. The checker verifies all these polynomial
identities using simultaneous substitution. Both changed witnesses
are positive integers.

Conversely, for any positive 81-operation solution, the independent
argument in Sections 2-3 proves q_new=2^(2mt) and v=2^m with
m,t>=1. Define

    q_old=2^(mt)=sqrt(q_new),
    quot_old=2^(m(t-1))=q_old/v.                  (10)

These are positive integers, including quot_old=1 when t=1.
Every unchanged abbreviation has precisely the old value, so all
20 predecessor equations hold. Also

    q_old*quot_old=2^(m(2t-1))=q_new/v=quot_new,

where the last equality is the retained first equation of (2).
Thus (9) and (10) are inverse maps. No auxiliary Pell witness needs
to be reconstructed, and no parity or positivity assumption is
lost: those witnesses and r are identical under the maps.

## 5. Exact scope and evidence boundary

For positive I,F, the new system has a positive solution if and only
if I is a Boolean base-four word and, for some positive height t,
the finite zero-exterior moving update b -> 4*Rule110(b), starting
at 4I, reaches 4F in t steps, with at least one pretransition row
containing 111. The latter condition is exactly what supplies the
positive E plane. This is the full endpoint characterization already
proved for the predecessor; the bijection preserves every solution.

In particular, all-positive necessity follows by applying (9) to
the predecessor's complete witness construction. A sufficiently
large row width m gives q_new=W^t and
quot_new=2^(m(2t-1)), while all existing coding and Pell witnesses
are retained.

The previous sparse-field and boundary regressions remain applicable
because they are expressed in the unchanged values Q,W and the local
planes. A new numerical search is unnecessary for this exact
reparameterization. The fresh symbolic source comparison verifies
the arithmetic change, while the general argument above establishes
the positive-domain bijection.

This finite-history endpoint relation is decidable: when a trajectory
exists, its height is the difference between the rightmost-one
positions of F and I. There is still no universal input or halt
interface. The proved universal certificate bound remains 90.
