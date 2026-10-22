# Independent review of the twelve-positive-unknown resultant

Reviewer: arithmetic_reduction; formulas supplied by fewer_variables.
This is an independent mathematical audit, not a proof-assistant check.

## 1. Monic polynomial identity

Use the normalized weighted-root definitions of package 09:

    I=i*c^2, D=1+Delta*I^2, Q=Delta*(D-1), d=Q-1,
    v0=c*T, b=c+R*D, P=Q*D*v0^2, Z=Q*b^2,
    e=P+Z-1, a0=P*Z,
    A=1+Lfirst*(Lfirst+k),
    M=2*(k*I^2+T^2), N=d*M^2*A.

For a formal variable v let

    H8(v) = [v^4-2*d*(N+e)*v^2
             +d^2*((N-e)^2+4*a0)]^2
             -16*a0*d^2*[v^2+d*(N-e)]^2.

This is monic of degree eight in v. For t=v/d and

    C=d*t^2+N-e,
    U=C^2+4*(a0-d*t^2*N),
    Res13(t)=U^2-16*C^2*a0,

direct substitution gives H8(v)=d^4*Res13(v/d). In particular,
no vanishing leading coefficient is hidden in the new elimination.

## 2. Elimination of the main Pell coordinate

Set B=1+Delta*c^2, H=4*a+3, p=H*c and W=X+a*c+H*u.
The proposed polynomial is

    R12 = Res_v(H8(v),(W-p*v)^2-B).

Equivalently it is the norm, in Z[sqrt(B)], of
p^8 H8((W+sqrt(B))/p). The displayed expression is polynomial after
homogenization. At a zero, p>0 and H8 is monic, so a common root v
exists and is an algebraic integer.

If B is nonsquare, v=(W+sqrt(B))/p or its conjugate has degree two.
Its conjugate v' is also an algebraic integer. The norm of v-v' is

    -4*B/p^2 = -4*(1+Delta*c^2)/(H^2*c^2).

This must be an integer. It lies strictly between -1 and 0, because

    H^2-4*Delta=12*a^2+8*a-3 >=17,

and a,c are positive. This is a contradiction. Hence B is square.
Then v is rational and, being an algebraic integer, is an integer.
The quantity gamma=u-c*v is therefore an integer and

    (X+a*c+H*gamma)^2-Delta*c^2=1.

This argument has no requirement that gamma or this Pell root be
positive. Such signs must be handled by the signed-domain compiler
theorem, as the proposed proof correctly does.

## 3. The remaining rational root is saturated automatically

The strengthened weight is twice package 09's low-degree weight.
That package proves N_old>e+1 under the weak outer bounds, including
equal index/transport unit signs. Therefore N>4*(e+1). In particular
C=d*t^2+N-e>0 for every rational t.

The t=0 case is impossible: then Res13=(C^2-4*a0)^2, while
C=N-e>e+1 and 4*a0=4*P*Z <=(P+Z)^2=(e+1)^2.

Package 09's algebra therefore applies with rational t. It reconstructs
a rational f with f^2=D; hence f is integral. It next reconstructs a
rational tau with tau^2=A; hence tau is integral. The remaining y is
initially rational, and satisfies

    Q*V^2-(Q-1)*y^2=1,

where V=c*(T*f-1)-R*f^2 is now integral and Q=S^2 with
S=Delta*i*c^2 >=2 integral.

The rational-y saturation claim is valid. Write S^2-1=b0^2*D0 with
D0 positive squarefree. The integer S>=2 implies D0>1. Put z=b0*y.
Then D0*z^2=(S*V)^2-1 is integral. Reduced denominators and
squarefreeness imply z is integral. Classify the integer Pell solutions
using the fundamental positive unit F0+G0*sqrt(D0):

    S=chi_F0(e0), b0=G0*psi_F0(e0),
    S*abs(V)=chi_F0(m0), abs(z)=G0*psi_F0(m0).

Here e0,m0>=1. The divisibility chi_F0(e0)|chi_F0(m0) forces
m0/e0 to be an odd integer. To verify this last claim, reduce m0
modulo 2*e0 and use chi(r+2e0)=-chi(r) modulo chi(e0), followed
by the reflection chi(2e0-r)=-chi(r). Every resulting representative
0<=r<e0 has 1<=chi(r)<chi(e0), leaving only r=e0. Thus
psi_F0(e0)|psi_F0(m0), and y=+-psi_F0(m0)/psi_F0(e0) is integral.

Since t=y+M*tau, t is also integral, and d divides the recovered v.
This is a mathematical consequence of the norm equation, not an
unstated divisibility hypothesis. The auxiliary root y cannot vanish,
because Q*V^2=1 is impossible for integral V and Q>1.

## 4. Signed-domain passage and completeness

The recovered f,tau,y may be signed, and gamma may be signed. Replace
tau and y by absolute values. If f<0, replace (f,T) by (-f,-T).
Every defining auxiliary expression depends on f through f^2 and T*f.
The normalized strong relation converts to the ordinary one by
i_ordinary=Delta*i>0. Package 12's signed-domain theorem then applies
with precisely its required positive coordinates J,F,alpha,z,i,s,w,
eta,zeta, and with T,gamma among the allowed signed coordinates.
No positive-gamma theorem may be substituted for this step.

Conversely start with a positive canonical normalized compiler witness,
take t=M*tau+y, v=d*t and u=gamma+c*v. These are positive integers.
H8(v)=0 and (W-p*v)^2=B hold, so R12=0. This proves existence
equivalence in both directions once the inherited compiler theorem is
composed.

## 5. Product compression

Write the norm evaluator as R12=Areal^2-B*Aimag^2 with integer
polynomials Areal,Aimag. Since Delta is 0 or 3 modulo 4 and c^2 is
0 or 1, B=1+Delta*c^2 is 0 or 1 modulo 4. Hence R12 is never 2
modulo 4. The factor 1+R12 cannot equal -1.

At a zero of Nk*Nt*(1+R12)-1 every factor is a unit, so R12=0 and
Nk,Nt have equal signs. The weak transport bounds needed above are
the same ones used for package 09's weighted proof. After restoration,
the signed Pell theorem recovers Nk=Nt=1. No unproved negative-sign
exclusion for the resultant is required beyond the simple modulo-four
argument just given.

## 6. Degree audit, independent of a generic sample

With original supplied variables of weight one and fixed compiler
numerals of weight zero, the package 09 degrees are

    deg(c)=5, deg(a)=6, deg(Delta)=12, deg(R)=4,
    deg(I)=11, deg(D)=34, deg(Q)=46,
    deg(P)=92, deg(Z)=122, deg(e)=122,
    deg(a0)=214, deg(M)=23, deg(N)=114.

The constant term of H8 has degree 672, with unique highest part
d_top^4*e_top^4. Its v^2,v^4,v^6 coefficients have degrees at most
504,336,168 respectively. In homogenization p has degree 11,
W has degree 11, and B has degree 22. The real part of
p^8 H8((W+sqrt(B))/p) consequently has degree 760 from the
constant coefficient times p^8. Every other term has degree at most
592. Its sqrt(B) coefficient has degree at most 581. Therefore the
norm has exact degree 1520: the second norm term has degree at most
22+2*581=1184 and cannot cancel the square of the real leader.
The product equation has exact degree 1529 when deg(Nk)=7 and
deg(Nt)=2; their leading forms are nonzero for every admissible beta>0.

## Verdict

The proposed twelve-variable elimination is sound under its stated
inherited normalized compiler and signed ordinary-Pell interface.
Its decisive new ingredient is the rational-y saturation lemma. The
conjugate-difference norm correctly excludes nonsquare B and removes
the main root without an extra divisibility variable. The numerical
operation ledger and concrete implementation remain separate audits.
