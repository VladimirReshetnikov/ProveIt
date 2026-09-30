# A strong half-binomial Pell kernel in42 operations

The retained fixed-minus kernel has a **42=25M+17A** variant. It keeps
the full strong auxiliary square and supplies the main Pell index R
directly. Its first Pell coefficient is doubled, while its ratio interval
is unchanged. Consequently it extracts **half** the binomial-floor word,
which raises the required binary population threshold by one.

This note proves the exact positive kernel projection under explicit
external scale/index bounds. The literal containing source has
**75=41M+34A**,30 positive witnesses and19 equations, as audited in
[the candidate source](complete75_half_binomial.py). A complete compiler,
mask, synchronization, dummy-adjustment and input theorem for that source
is separate work. The complete75 composition is proved in
[the reviewed universal theorem](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).
Author and independent full proof/source/default reviews pass.

## 1. Exact source and theorem

Suppose the containing arithmetic supplies an integer q and main index R
with the already paid common scale D0, satisfying

    q>=16, D0=q^3, 3q+1<=R<q^4.                         (1)

These are theorem hypotheses, not free instructions of the42-operation
kernel. In the containing source the two products q*q and(q*q)*q already
occur in the outer packing. In particular this statement does not require
R>=q^2 or assume q is a power before decoding.

Besides D0,R supply sixteen strictly positive coordinates

    a,c,d,f,h,i,j,K,o,s,w,T,eta,zeta,gamma,y.

The checker retains the source names k,tau,ga,y_aux for K,T,gamma,y and
aliases its legacy register r to R. Define computed abbreviations

    X=wD0, Y=sD0, E=XY, A=a+2, Delta=A^2-1,
    H=4a+3, rho=i*c^2, U=j*c-R.

The ten equations are

    (E^2+X)(KY)^2=T^2-1,
    c=KY+eta, K=eta+zeta,
    K=R+1+hE, a=Y(X+1),
    d=X+ac+gamma*H,
    d^2=1+Delta*c^2,
    rho^2=Delta*(f^2-1),
    rho^2*(U^2-y^2)=1-y^2,
    U=of-c.                                            (2)

All displayed powers and products in(2) use the literal counted source;
rho and U are computed registers, not extra witnesses. The independently
written penultimate polynomial uses Delta*(f^2-1) in place of rho^2.
The checker verifies its usual acyclic correction by the preceding norm
residual times U^2-y^2.

Under(1), the exact projection of(2) is

    q=2^t for an integer t>=4,
    R=3 modulo4,
    popcount((R-1)/2)>=3t+1.                            (3)

Writing r0=(R-1)/2 and

    xi=(X+1)^(2r0)/X^r0,

every positive solution additionally satisfies

    X=2^R, Y=floor(xi)/2,
    c=psi_A(R), d=chi_A(R),
    K=2*psi_(2XY^2+1)((R+1)/2).                         (4)

Since R is odd, (3)'s population condition is equivalently
`popcount(R)>=3t+2`.

## 2. Exact one-operation saving

The original43 kernel computes

    tauplus1=tau+1; norm_right=tau*tauplus1;
    r1=r+1; index_rhs=r1+hE; main_index=r1+r;
    U=jc-main_index.

Here hE is one product, and r1 is shared by the first and main indices.
Simply doubling the old first-index equation without changing the norm
would save nothing.

The new source instead computes

    tau_square=T*T; norm_right=tau_square-1;
    r1=R+1; index_rhs=r1+hE;
    U=jc-R.

Its norm still costs one product and one addition/subtraction. The one
addition `main_index=r1+r` is deleted. No computed2K or2c is present;
the altered Pell norm proves that the supplied K is even. Every other
primitive, including `(i*c^2)^2`, remains. Thus43 becomes42 without
weakening the auxiliary rank equations.

The checker imports the actual76 source and verifies that the full75
schedule in complete75_half_binomial is exactly these edits, with only
the fixed mask numeral replaced by MF+B-1. This fixed numeral offset costs
no runtime operation. The ledger remains19 outer+42 kernel+14 input.
The algebraic source audit does not prove the changed compiler; its separate proof is now independently reviewed.

## 3. The first norm has no odd-coefficient escape

Put V=XY^2 and P=2V+1. The first equation in(2) is exactly

    T^2-V(V+1)K^2=1.                                  (5)

The integer V(V+1) is nonsquare: it lies strictly between V^2 and(V+1)^2.
For K=1 the possible square V^2+V+1 also lies strictly between those
squares, since V>=1. For K=2 the positive solution is T=2V+1.
Therefore the least positive Pell unit has coefficient2 and equals
`P+2*sqrt(V(V+1))`. All positive Pell solutions are its positive powers.
Equivalently, for some n>=1,

    T=chi_P(n), K=2*psi_P(n).                           (6)

This classification uses only X,Y>0. In particular it does not assume
that q, X, Y or any supplied coordinate is even beforehand. A putative
smaller square-root unit would have positive coefficient1, already
excluded by the strict square interval.

## 4. Strong rank and both exact indices, without a parity shortcut

Before any power conclusion, (1) and positivity give

    X,Y>=q^3, E>=q^6>2R,
    a=Y(X+1)>q^6>R, P>A, 6XY^2>a.                     (7)

Since P=1 modulo E, the psi recurrence gives psi_P(n)=n modulo E.
Thus K=R+1+hE and(6) imply

    2n=R+1 modulo E.

The representative R+1 lies strictly between0 and E, so
`n>=(R+1)/2`. No parity of R or E is assumed. The main norm gives
c=psi_A(p), d=chi_A(p) for p>=1. Since c>YK>psi_P(n) and P>A,
monotonicity gives p>=n+1. Consequently p>=6 and

    c>(2A-1)^(p-1)>A^5>A*(A^2-1)^2,
    c>2Yn>=Y(R+1)>2R,
    c>2p.                                             (8)

These are the hypotheses of the retained
[relaxed auxiliary-rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md).
It gives an auxiliary index m with

    f=chi_A(m), c|m, m>=c>2p, rho=Delta*psi_A(m)>1.

Apply the retained [half-parameter index argument](../../1980/HALF_PARAMETER_PELL_92_PROOF.md),
with the two minus congruences `U=-R mod c` and `U=-c mod f`.
U=j*c-R>0 by(8). Its normalized auxiliary Pell index is odd; the signed
step-down gives `R=+p or-p modulo c`. The possible alternative R+p=c
is excluded by **c>2R and c>2p**, rather than assuming R is odd. Thus

    p=R.                                              (9)

Because P>A and c>K, n<=p-1=R-1. Both2n and R+1 lie in(0,E), using
E>2R, so their congruence is the exact equality

    2n=R+1.                                           (10)

This now proves R is odd and n=(R+1)/2. Also f>2c follows from m>2p
and Pell growth. The [necessary fixed-minus parity theorem, Section4](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
applies to p=R and gives R=3 modulo4. All rank and parity deductions
precede mask decoding and use the full strong square equation.

## 5. Ratio bounds and power recovery

Let r0=(R-1)/2, k0=K/2=psi_P(r0+1), and
xi=(X+1)^(2r0)/X^r0. The unchanged elementary Pell estimates in
[the base-two proof, Section3](../../1980/BASE_TWO_PELL_89_PROOF.md) give

    c/k0 >= xi*(1+3/(2a))^(2r0)
                  *(1+1/(2XY^2))^(-r0) > xi,           (11)
    c/k0 < xi*(1+2/a)^(2r0)
           < xi*(1+8r0/a).                            (12)

The strict lower comparison follows from6XY^2>a. For the last upper
bound, `4r0/a<2/q^2<1/2`, already justified by(1),(7). The new interval
in(2) is `Y<c/(2k0)<Y+1`. Hence

    xi<2Y+2, Y>X^r0/2-1>X^r0/3,
    a>X^(r0+1)/3.                                     (13)

The final strict lower bound uses X>=4096 and r0>=24. This is established
before using a small ratio error or interpreting an exponent congruence.
Since Y>1, (11)–(13) give the sufficient error estimate

    0<c/K-xi/2<16r0/(X+1).                            (14)

For a direct proof of exponent recovery, the sequence
`chi_A(j)-a*psi_A(j)` has initial values1,2 and the Pell recurrence.
Modulo H=4a+3 that recurrence agrees with2^j, since4A-1=4 modulo H.
The source therefore gives X=2^R modulo H. Both positive representatives
lie below a: X<a trivially, and

    2^R=2*4^r0 < X^(r0+1)/3 < a,                      (15)

using X>=4096. Thus X=2^R exactly. Since q^3 divides X, q=2^t. No
square-root scale or prematurely even q is used in this step.

Now the right side of(14) is below1/2. Expand

    xi=M+theta,
    M=binom(2r0,r0)+sum_(j=1)^r0 binom(2r0,r0+j)*X^j,
    theta=sum_(j=1)^r0 binom(2r0,r0-j)/X^j.             (16)

Here0<theta<1/4: the sum of the lower half's binomial coefficients is
less than2^(2r0-1), while X=2^(2r0+1). Also M is even because X is
even and the positive central binomial coefficient is even. Consequently

    M/2<c/K<M/2+1/8+1/2<M/2+1.

The same quotient lies strictly between the integer Y and Y+1, forcing
Y=M/2=floor(xi)/2. This is the changed extraction theorem; the old
unhalved conclusion must not be reused.

## 6. Exact valuation and the positive converse

The central-binomial valuation identity gives
`v2(binom(2r0,r0))=popcount(r0)`. This valuation is below R. Every other
term of M in(16) is divisible by X=2^R. Therefore

    v2(Y)=popcount(r0)-1.                              (17)

Since Y is a multiple of q^3=2^(3t), (17) proves(3). For odd R,
`popcount(R)=popcount(r0)+1`, giving the equivalent threshold3t+2.

Conversely take q,R satisfying(1),(3). Put r0=(R-1)/2, X=2^R, define
M,theta by(16), and Y=M/2. Then w=X/q^3 and s=Y/q^3 are positive
integers. Scale integrality follows from R>=3q+1>3log2(q) and(17);
there is no assumption q^3<r0^2. In fact Y>=X^r0/2, so all necessary
growth inequalities hold at the actual new Y.

Set

    a=Y(X+1), A=a+2, Delta=A^2-1, E=XY, P=2XY^2+1,
    c=psi_A(R), d=chi_A(R),
    k0=psi_P(r0+1), K=2k0, T=chi_P(r0+1),
    eta=c-KY, zeta=K-eta,
    h=(K-R-1)/E, gamma=(d-X-ac)/(4a+3).                 (18)

The ratio proof at these parameters gives Y<c/K<Y+1, so eta,zeta are
strictly positive integers. The first recurrence modulo E proves
`h=2*(k0-(r0+1))/E` integral, and strict Pell growth makes it positive.
The exponent recurrence makes gamma integral. Its numerator is positive:
`d-ac=2c-psi_A(R-1)>c>X`, so gamma>0.

For the remaining strong auxiliary witnesses, use the unchanged canonical
minus construction at these **fresh** A,c,R:

    m=2cR, f=chi_A(m), i=Delta*psi_A(m)/c^2,
    rho=i*c^2, y=psi_rho(R), U=chi_rho(R)/rho,
    o=(U+c)/f, j=(U+R)/c.                              (19)

The retained rank/divisibility construction makes i integral and positive.
R=3 modulo4 gives the minus congruences U=-c modulo f and U=-R modulo c,
so o,j are integers. The ordinary growth bound U>c>R makes them positive.
All other coordinates in(18)–(19) are positive, and direct substitution
verifies all ten source equations. No identity map from the former
kernel's auxiliary values is asserted: Y, A and their Pell witnesses
have changed.

## 7. Evidence and exact limits

The [checker](pell_kernel_half_binomial42.py) and
[receipt](pell_kernel_half_binomial42.json) audit every42 primitive and
independent residual, with the strong-norm correction. They compare the
whole75 schedule against the actual76 source edits and call the
separate candidate source auditor rather than maintaining a duplicate
compiler schedule.

They also check260 pre-power parameter cases,2,000 generated first-norm
points,8,000 arbitrary first-norm coefficients, seven exact main prototypes,
and700 half-binomial valuation cases. The first-norm proof is parametric;
finite searches are supplementary.

A complete numerical42 tuple is materialized at R=3,D0=1:

    X=8,Y=5,a=45,c=8835,K=1604,T=321601,
    eta=815,zeta=789,h=40.

All sixteen auxiliary coordinates are positive and all ten equalities
hold; the largest have fewer than700,000 bits. This example is explicitly
outside the q>=16 theorem hypotheses and is not a complete75 compiler
instance. The large witnesses in the theorem are supplied parametrically
by(18)–(19), not by finite tests or this small example.

Replay with

    /tmp/diophantine-research-venv/bin/python pell_kernel_half_binomial42.py

Review status: author and two independent full proof/source/default reviews
pass. A further independent proof review of the changed positive converse
and unchanged input bridge also passes. These reviews establish this kernel
interface; the full compiler composition is reviewed separately.
