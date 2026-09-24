# A complete counterexample to the radix-sixteen deleted-bound edit

The proposed 79-operation edit of the published 80-operation finite-history
component is unsound. It changes the local radix from eight to sixteen,
uses a shorter Boolean-mask word, and deletes the positive field bound.
The explicit tuple below satisfies every outer equation, passes the complete
packed Boolean mask, and extends to all-positive witnesses for the retained
43-operation Pell subsystem. Its positive output parameter is not Boolean
in radix sixteen. Thus the edit does not express the intended history relation.

The published 80-operation component and the universal 90-operation
certificate are unchanged. This is a search boundary, not a new upper bound.

## 1. The precise rejected system and arithmetic

The parameters are positive I,F. The eleven positive outer unknowns are

    q,v,quot,H,B,C,Y,U,V,alphaI,lambda.

The seventeen positive Pell unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

Define the following abbreviations; all required arithmetic is included in
the complete checker, rather than treating these expressions as free:

    W=v^4, L=q^4, D0=q^7,
    T=B+H, P=U+qV+q^2Y+q^3T,
    U_pell=wD0, Y_pell=sD0,
    D_pell=a^2+4a+3, K=D_pell(f^2-1), u=2r+1+jc.

The eight outer source equations are

    q=v*quot,
    q-1=H(W-1),
    B=16C,
    31B+4Y=C+2U+3V,
    I+alphaI=v,
    I+WY=C+qF,
    15lambda+1=L,
    r=(L-P)15lambda+14lambda.                         (1)

In particular the equation C+2U+3V+alpha=q is absent. The ten retained
Pell equations are

    U_pell*Y_pell^2*(U_pell*Y_pell^2+1)*k^2=tau(tau+1),
    c=Y_pell*k+eta,
    k=eta+zeta,
    k=r+1+h*U_pell*Y_pell,
    a=Y_pell*(U_pell+1),
    d=U_pell+a*c+gamma*(4a+3),
    d^2=D_pell*c^2+1,
    (i*c^2)^2=D_pell*(f^2-1),
    K*(u^2-y_aux^2)=1-y_aux^2,
    u=c+o*f.                                        (2)

The power chain q^2,q^3,q^4,q^7 has four multiplications, as does
the predecessor's chain q^2,q^4,q^6,q^10. The row power v^4 still
costs two multiplications. Changing the fixed coefficients costs nothing
in the free-numeral convention. Deleting the field bound removes exactly
one addition. Thus the rejected schedule has

    79 = 46 multiplications + 33 additions/subtractions,
    28 positive unknowns and 18 equations.

The checker
`../verification/explore_radix16_deleted_history_bound.py`
defines all 79 primitives and fresh source polynomials (1)-(2), and its
adjacent JSON serializes every primitive and every source comparison.
The only nonzero residual adjustment is acyclic: in the penultimate
equation the schedule uses the existing register (ic^2)^2 for K.
The difference from the displayed source residual is exactly

    ((ic^2)^2-D_pell*(f^2-1))*(u^2-y_aux^2),          (3)

the preceding source residual multiplied by the indicated polynomial.

## 2. Exact outer witnesses and the carry cancellation

Use the positive parameters and witnesses

    I=1, F=250609653,
    q=16777216=16^6, v=4, quot=4194304,
    W=256=16^2, H=65793,
    B=8208, C=513,
    U=14706018353152,
    V=12094593474557,
    Y=16423954219010,
    alphaI=3.

In particular q=W^3 and H=1+W+W^2. The geometric and strong input
guard equations hold exactly. Set

    a_carry=876547, b_carry=720894, c_carry=978944,
    T0=1052945=0x101111.

These integers satisfy

    U=q*a_carry,
    V=q*b_carry-a_carry,
    Y=q*c_carry-b_carry,
    B+H+c_carry=T0.                                 (4)

Consequently all three field carries cancel in the complete packing:

    P=U+qV+q^2Y+q^3(B+H)=q^3*T0
      =4972392176305178579535134720.                (5)

Every radix-sixteen digit of P is zero or one, and 0<P<q^4. Thus this
is a counterexample even to a direct Boolean test of the entire packed
word; it does not rely on a weakness in the popcount implementation.
The omitted field bound is what permits its individual fields to overlap.

Direct integer evaluation also gives

    31B+4Y=C+2U+3V,
    I+WY=C+qF.                                     (6)

The exact regression evaluates all eight source residuals and the actual
36-instruction outer schedule, obtaining zero for each equality. Set
L=q^4, lambda=(L-1)/15, and choose r from the last equation of (1).
These are positive integers. Hence every outer unknown is positive.

The output parameter is

    F=0xEEFFFF5,

with radix-sixteen digits, from low to high, 5,15,15,15,15,14,14.
It is not a Boolean endpoint. No finite Boolean Rule 110 history with
the stated numerical endpoint relation can end at this F.

## 3. Exact mask valuation and the original square-scale interface

For this concrete tuple, the Pell scale is an actual square:

    D0=q^7=2^168,
    n0=sqrt(D0)=2^84=19342813113834066795298816.

There is no need to invoke a generalized nonsquare-scale interface.
The regression verifies exactly

    n0>=64, n0^2<r<n0^3,
    r is even,
    popcount(r)=168.                                (7)

These facts can also be read from (5) and the radix-sixteen special-mask
identity: L=16^24 and its maximal popcount threshold is 7*24=168.
The least bit of P is zero, so the mask's parity identity gives even r.
The direct arbitrary-precision calculation verifies both facts without
using that identity as an implementation assumption.

Kummer's identity for the central binomial coefficient gives

    v_2(binom(2r,r))=popcount(r)=168.

Thus D0 divides the central binomial coefficient, with precisely the
required valuation. All original square-scale positive-kernel hypotheses
are available before any Pell witnesses are chosen: n0 is a power of two,
n0<=r<2n0^3, r is even, and n0^2 divides binom(2r,r).

## 4. Extension to every positive Pell witness

Apply the positive retained construction proved in
`BASE_TWO_PELL_90_PROOF.md` and `HALF_PARAMETER_PELL_92_PROOF.md`,
also spelled out for this isolated kernel in Section 7 of
`EXPLORATION_TWO_AUXILIARY_HISTORY.md`. It uses the range, parity,
and divisibility conditions (7); it does not use Booleanity of the outer
fields or the omitted field-bound equation.

Explicitly, put

    J=2r+1, U_pell=2^J,
    Y_pell=floor((U_pell+1)^(2r)/U_pell^r),
    w=U_pell/D0, s=Y_pell/D0,
    a=Y_pell*(U_pell+1), A=a+2,
    c=psi_A(J), d=chi_A(J),
    P_pell=2U_pell*Y_pell^2+1,
    k=psi_(P_pell)(r+1).

The power-of-two and central-binomial divisibility make w,s positive
integers. The proved strict ratio estimates give

    eta=c-Y_pell*k>0, zeta=k-eta>0.

The remaining first-norm and congruence witnesses are

    tau=(chi_(P_pell)(r+1)-1)/2,
    h=(k-r-1)/(U_pell*Y_pell),
    gamma=(d-U_pell-a*c)/(4a+3).

Their integrality and strict positivity are exactly the odd-parameter
norm, index-congruence, and first-exponential necessity arguments of the
cited base-two proof. No second-index or second-exponent equation is
present in (2).

For completeness the relaxed auxiliary construction can take

    m_aux=2cJ,
    f=chi_A(m_aux),
    i=D_pell*psi_A(m_aux)/c^2,
    R=i*c^2.

The standard divisibility in the relaxed-auxiliary necessity proof makes
i a positive integer. Set

    y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

Since even r gives J=1 modulo 4, the half-parameter polynomial
congruences make both o and j integers. The growth proof gives
u>c>J, hence their positivity. The half-parameter norm is precisely
the last norm in (2). These choices supply all seventeen positive
Pell unknowns and complete the full-system counterexample.

The regression does not construct numbers such as 2^(2r+1). It checks
the exact finite hypotheses used by this general existence proof, while
its symbolic phase verifies the complete 79-operation source system.
This separates the reproducible finite calculation from the proved
positive extension; neither is presented as a numerical evaluation of
the enormous complete Pell tuple.
