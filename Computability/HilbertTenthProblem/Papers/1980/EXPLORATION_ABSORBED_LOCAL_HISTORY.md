# Absorbing the spatial shift: the same history relation in 79 operations

The finite Rule 110 history relation proved in
`EXPLORATION_TWO_AUXILIARY_HISTORY.md` has a 79-operation certificate:
46 multiplications and 33 additions or subtractions, with the same
29 positive unknowns, 19 equations, and positive endpoint parameters I,F.
This saves one addition from the published 80-operation component.
The finite endpoint relation is unchanged. No universal input or halt
interface is claimed, and the published universal bound remains 90.

The saving combines the spatial equation B=8C with the scalar local
relation and adjusts the positive shared bound. It retains a bound on
every packed field. The required pre-Pell estimates are proved anew below;
the argument does not apply the old proof to an unproved positive old slack.

## 1. The exact change and primitive accounting

The old local equation and bound were

    15B+4Y=C+2U+3V,
    C+2U+3V+alpha_old=q.

Retain B=8C, and replace those equations by

    119C+4Y=2U+3V,
    2U+3V+alpha=q.                                  (1)

The coefficient is 119=15*8-1. Fixed numerals are free, but their
use in multiplication is counted. The old local schedule had seven
operations:

    15B, 4Y, 15B+4Y, 2U, 3V, C+2U, C+2U+3V.

The new schedule has six:

    119C, 4Y, 119C+4Y, 2U, 3V, 2U+3V.

In either case the slack equation takes one further addition to the
already computed right side. The spatial multiplication B=8C remains
counted, as does every operation in the packing, geometry and Pell block.
Thus the saving is exactly one addition, not a free scalar multiplication.

The complete checker
`../verification/round45_1980_absorbed_local_history.py`
contains an explicit 36-instruction outer schedule and the retained
43-instruction Pell schedule. Its JSON receipt serializes all 79 primitives,
all 19 equality tests, and fresh source polynomials. The only triangular
source adjustment in the Pell schedule is unchanged from the predecessor:
the penultimate residual differs by

    ((ic^2)^2-D_pell*(f^2-1))*(u^2-y_aux^2),

using the preceding exact auxiliary equation. No circular residual
substitution is introduced.

## 2. Complete source system

The twelve positive outer unknowns are

    q,v,quot,H,B,C,Y,U,V,alpha,alphaI,lambda.

The seventeen positive Pell unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

Use the abbreviations

    W=v^3, L=q^6, D0=q^10,
    T=B+H, P=U+qV+q^2Y+q^3T,
    U_pell=wD0, Y_pell=sD0,
    D_pell=a^2+4a+3,
    K=D_pell*(f^2-1), u=2r+1+jc.

The nine outer equations are

    q=v*quot,
    q-1=H(W-1),
    B=8C,
    119C+4Y=2U+3V,
    2U+3V+alpha=q,
    I+alphaI=v,
    I+WY=C+qF,
    7lambda+1=L,
    r=(L-P)7lambda+6lambda.                         (2)

The ten retained Pell equations are

    U_pell*Y_pell^2*(U_pell*Y_pell^2+1)*k^2=tau(tau+1),
    c=Y_pell*k+eta,
    k=eta+zeta,
    k=r+1+h*U_pell*Y_pell,
    a=Y_pell*(U_pell+1),
    d=U_pell+a*c+gamma*(4a+3),
    d^2=D_pell*c^2+1,
    (ic^2)^2=D_pell*(f^2-1),
    K*(u^2-y_aux^2)=1-y_aux^2,
    u=c+o*f.                                        (3)

## 3. The new bound supplies every preliminary kernel hypothesis

Suppose arbitrary positive integers satisfy (2)-(3). The input slack
gives v>=2. The row geometry gives q>=W=v^3>=8. Positivity and (1)
give the strict bounds

    C<q/119,
    B=8C<8q/119<q/8,
    Y<q/4, U<q/2, V<q/3.                           (4)

Also H=(q-1)/(W-1)<q/7, so

    T=B+H<(8/119+1/7)q=25q/119<q.                 (5)

All four packed fields are positive integers below q. Hence

    0<P<q^4<L=q^6.

The last equation of (2) therefore gives

    r>(q^6-q^4)(q^6-1)>q^5,
    r<q^12.                                        (6)

For the upper bound, P>=1 and 6lambda<L-1 yield
r<(L-1)^2+(L-1)<L^2. Put n0=q^5. Then

    n0>=64, n0<r<n0^3,
    D0=n0^2, U_pell,Y_pell>=n0^2.                 (7)

These are precisely the preliminary bounds used by the retained
43-operation kernel in Sections 3-4 of the predecessor proof. That
kernel's first-index, first-exponent, and rounding arguments use (7),
positivity, and (3); they do not use a decoded Boolean field or the
old expression C+2U+3V<q. Thus the unchanged base-two Pell proof applies
in the same noncircular order. It yields

    U_pell=2^(2r+1),
    D0 divides binom(2r,r).                        (8)

Since q^10 divides U_pell, q is a power of two. Since v divides q,
v is a power of two as well. Write v=2^m. The geometric divisor
v^3-1 divides q-1, so the elementary power divisibility criterion gives

    W=8^m, q=W^t=8^(mt),
    H=1+W+...+W^(t-1),                            (9)

for positive integers m,t. In particular every field boundary is now
aligned with radix-eight digits, before extracting any field.

Write q=2^e. Then L=q^6=8^(2e). The general radix-eight mask lemma
has maximum popcount 5*(2e)=10e. Equations (8) and the central-binomial
valuation identity give a popcount at least 10e, hence equality.
The mask lemma therefore makes P Boolean in radix eight. Its four
bounded aligned fields U,V,Y,T are each Boolean.

## 4. Causal recovery of the source field and the local rule

The generic subtraction and causal argument of the predecessor applies
with all of its range hypotheses now established by (4)-(5). Here are
the relevant steps explicitly.

Width m=1 is impossible: H=(q-1)/7 is then already the largest Boolean
word below q, whereas Boolean T=B+H is strictly larger. Thus m>=2,
v>=4, and I<v<=W/8. Both C and Y are below q. The temporal equation,
I<W and positivity imply F<W, so its base-W row decomposition gives

    c_0=I,
    c_(j+1)=y_j for j<t-1,
    y_(t-1)=F.                                     (10)

Subtracting H from Boolean T shows that every row-start digit of B
is one of 0,6,7. A zero start has zero outgoing borrow and makes that
entire B row Boolean. Since B=8C, its first digit is zero. The highest
digit of c_0=I is zero because I<W/8; it is the start of the next B row.
Every subsequent C row in (10) is a Boolean Y row. Its highest digit
is therefore zero or one, but that digit is also the following B row
start and belongs to {0,6,7}. It must be zero. Induction makes all of
B Boolean, with every row start zero.

The words A=8B and C=B/8 are now Boolean, and (4) gives A<q. Rewriting
the local equation with B=8C yields exactly

    2A+4Y=B+C+2U+3V.                               (11)

Each nonnegative raw digit on the left is at most six and on the right
at most seven. There are no radix-eight carries in (11). Thus at every
cell it states

    2a-b-c+4y=2u+3v.

For Boolean a,b,c,y,u,v this holds for unique u,v if and only if y
is Rule 110(a,b,c). This is the complete scalar table proved in the
predecessor; it gives u=a XOR (bc), v=b XOR c. Therefore Y is the
actual local update and U,V are its intended auxiliaries.

The zero row starts resolve the left seam, where Rule 110(a,0,c)=c
does not depend on the possibly adjacent-row left input. The spatial
right input is zero at each row end. Since Rule 110(a,0,0)=0, the
exterior contributes no omitted occupied cell. Equation (10) then
gives the finite zero-exterior moving update b -> 8*Rule110(b), from
8I to 8F. This is the same seam argument as in Section 6 of the
predecessor, with A<q and B<q/8 both verified in (4).

In particular the highest packed B digit is zero by (4). At the
highest position, its right neighbor is zero, so the highest Y digit
is also zero. Thus both Boolean words have a blank highest digit and

    B <= (q/8-1)/7 < q/56,
    Y <= (q/8-1)/7 < q/56.                          (12)

This also proves F<W/8, so the final moving row fits within its width.
As before, the rightmost nonzero source digit supplies a one in V and
the following cell supplies a one in U; B<q/8 ensures that following
cell is within the packed range. There is no extra 111 condition.

## 5. An explicit positive bijection of all source witnesses

There is a positive witness bijection with the published 80-operation
source, keeping every supplied coordinate except alpha fixed:

    alpha_new=alpha_old+C,
    alpha_old=alpha_new-C.                          (13)

The forward map is immediately positive. Its local residual identity
is

    (119C+4Y-2U-3V)
      =(15B+4Y-C-2U-3V)-15(B-8C),

and its bound residual is the old bound after (13). The checker verifies
the complete forward substitution on all nineteen fresh source residuals,
not just the two changed equations.

For the inverse, positivity must be proved rather than assumed. Starting
from an arbitrary new positive solution, Sections 3-4 first establish
all the decoding conclusions without using alpha_old. Now (12) gives

    C+2U+3V=15B+4Y<19q/56<q.

It follows that

    alpha_new-C=q-(C+2U+3V)>0.

Thus the inverse in (13) is a positive integer, all old equations hold,
and the two maps are inverse on the full sets of positive witnesses.
This is stronger than an endpoint equivalence and makes explicit where
the apparently weaker new bound recovers the old one.

## 6. All-positive necessity and exact scope

For every intended finite moving history, the predecessor construction
chooses a sufficiently wide radix-eight rectangle with two blank high
columns, all positive U,V,Y, and positive alpha_old. Apply the forward
map in (13); every outer witness remains positive. The packed P, mask
lambda, r, q and all seventeen Pell witnesses are unchanged. In particular
r remains even, D0 divides the central binomial coefficient, and the
complete canonical positive kernel construction still applies. It needs
no new parity, congruence or endpoint assumption.

Consequently this 79-operation system defines exactly the positive
endpoint relation of the published 80-operation system: I,F are Boolean
radix-eight words and some positive number of finite zero-exterior moving
Rule 110 steps carries 8I to 8F. Its height is determined by the difference
of the highest occupied positions of F and I, so it is still a decidable
endpoint predicate. This result improves the arithmetic size of that
history component, not the universal 90-operation certificate.

The complete symbolic checker and source bijection are exact algebraic
checks. They do not substitute for the noncircular decoding and inverse
positivity proof above, and no enormous Pell tuple is materialized by
the checker. The predecessor's finite canonical examples transfer by
(13). The separate
`../verification/explore_eliminated_center_history_audit.py` and its JSON
receipt test the weaker bound directly over 19,724 complete candidate
T words, yielding 17 positive accepted tuples and 30 canonical histories.
Fifteen accepted tuples have no source 111 pattern. Every enumeration
filter uses 119C+4Y<q; the old bound is checked only after acceptance.
The audit verifies the actual moving trajectories, both positive slack
maps, input/output Booleanity, field ranges, even r and the exact mask
popcount. The full proof and source schedule also passed an independent
review. These checks corroborate the general proof without materializing
the enormous Pell witnesses or establishing a universal interface.
