# Selective coprime products and staged square recovery

Research note, 25 October 2026. Comparison snapshot:
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`.
All equations use the entire indexed943/radix67 four-port tuple
`beta,K0,MC,MF`. MF is already shifted.

## Completed endpoints and inherited interface

| Literal graph | Positive unknowns | Operations | Exact degree |
|---|---:|---:|---:|
| equation_14_raw.json | 14 | 70 | 189 |
| equation_14_reduced.json | 14 | 71 | 157 |
| equation_13_anchored.json | 13 | 72 | 433 |

An operation is one binary addition, subtraction or multiplication,
including multiplication by a small constant and squaring. Reuse and
fixed integer leaves are free. The exact source graphs and coefficient
payloads, rather than only an unspecified recipe, are supplied.

The parent is the fifteen-positive P66 circuit, with 66 operations and
degree 157. Its frozen graph and ordinary proof are under `parents/`.
That proof supplies two interfaces: a positive parent zero yields a
finite syntactic ZFC refutation; conversely a finite refutation supplies
canonical positive outer witnesses, with R=3 modulo 4, and the stated
main/strong/auxiliary Pell completions.

Coprime product-square extraction and imposing divisibility on a free
Pell multiplier have explicit predecessors in the repository. No novelty
is claimed for those general ideas. This contribution selectively applies
them to P66's inexpensive arithmetic and recovers a previously removed
square root before excluding a negative unit. The order of that reasoning
allows one copy of the first radicand to replace its square. The separate
thirteen-variable construction adds two inexpensive coprimality anchors.

The active comparison review records fourteen-positive endpoints 73/342,
74/312, 75/293 and 76/191. The new 70/189 and 71/157 points improve that
specific arithmetic frontier. These are not global minimality claims.
Other variable counts and degrees remain separate optimization objectives.

## 1. Common outer polynomial abbreviations

All input variables are strictly positive integers. Retain from P66

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, ell=E*k*Y, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a*a+H=(a+2)^2-1,
    D=X+a*c+gamma*H,
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J,
    N1=D*D-Delta*c*c,
    Nk=k-h*E-R,
    Nt=(K0+w)*C+(q-F)-z*(q-1),
    A=1+ell*(ell+k).

A is the first Pell radicand. The main Pell base is a+2, a different
quantity. Positivity of the inputs and beta>0 imply A>1,c>1,Delta>0,D>0.
Every definition is a polynomial abbreviation, not another variable.

## 2. Fourteen variables, 70 operations, degree 189

The quantified coordinates are

    J,F,alpha,z,f,h,i,T,s,w,eta,zeta,gamma,t > 0.

Define

    I=i*c^2,
    W=Delta*A*I^2,
    Q=Delta*W=A*(Delta*I)^2,
    Ns=f^2-W,
    V=f^2*(c*T-R)-c,
    Eprod=Q*(t^2-A*V^2)-t^2+A,
    U=3*Eprod+1.

The equation is

    N1*Nk*Nt*U*Ns-1=0.                       (P14r)

The graph shares Delta*c^2 from N1, evaluating
I=i*c^2, S0=i*(Delta*c^2), W=A*(I*S0), Q=Delta*W.
Its factored Eprod equals

    (Q-1)*t^2-A*(Q*V^2-1).                  (1)

### Soundness: recover A before excluding the strong negative unit

At a zero every factor is an integer unit. U cannot be -1, since U=1
modulo 3. N1 cannot be -1 because Delta is 0 or 3 modulo 4, so N1 is
a square or a sum of two squares modulo 4. Therefore

    U=N1=1, Eprod=0, Nk*Nt*Ns=1.

We do not yet assert Ns=1. The expression W is not known to be Delta
times an integer square at this stage.

Q>1 and A divides Q unconditionally. Write B=Q-1 and Caux=Q*V^2-1.
Equation (1) gives

    B*t^2=A*Caux.                            (2)

Moreover B=Caux=-1 modulo A, so

    gcd(A,B)=gcd(A,Caux)=1.

For every prime p dividing A, valuation in (2) gives
2*v_p(t)=v_p(A). Hence A=tau^2 for an integer tau>0, and tau divides t.
Set y=t/tau>0. Cancelling tau^2 in (2) gives

    tau^2=1+ell*(ell+k),
    Q*V^2-(Q-1)*y^2=1.                       (3)

Only now use A=tau^2. It gives W=Delta*(tau*I)^2. Thus Ns cannot be
-1 modulo 4, by exactly the same square-residue argument used for N1.
Since Ns is an integer unit, Ns=1, and consequently Nk*Nt=1.

Restore the parent multiplier as i_old=tau*i. Then

    f^2=1+Delta*i_old^2*c^4,
    Q=(Delta*i_old*c^2)^2.

Equations (3) restore the parent first and auxiliary norms. Along with
N1=1 and Nk*Nt=1, they give a positive zero of the original P66 equation.
No assertion about the sign of V was used here; its later recovery is
part of the inherited parent soundness proof.

## 3. Fourteen variables, 71 operations, degree 157

Use the same fourteen quantified coordinates, but define

    m=A*i, I=m*c^2, S=Delta*I,
    W=I*S=Delta*I^2,
    Ns=f^2-W,
    Q=Delta*(f^2-1),
    V=f^2*(c*T-R)-c.

Keep Eprod=Q*(t^2-A*V^2)-t^2+A and U=3*Eprod+1, with the same
product equation

    N1*Nk*Nt*U*Ns-1=0.                       (P14d)

This time Ns is a genuine normalized Pell norm before any extraction,
so the modulo-4 argument excludes Ns=-1 immediately. Thus

    Ns=N1=U=1, Nk*Nt=1,
    Q=Delta*W=S^2.

A divides S, so the identical coprime extraction in (2) gives positive
tau,y with A=tau^2 and Q*V^2-(Q-1)*y^2=1. Restoring i_old=m gives
an exact parent P66 zero.

The raw and reduced equations are different parameterizations; no claim
of equality of their complete fourteen-coordinate zero sets is needed.
Both have zero existence equivalent to the same calibrated source.

## 4. Cofinal strong Pell multipliers

A canonical source completion supplies a positive strong pair f0,j0 with

    f0^2=1+Delta*j0^2*c^4.

For any positive integer modulus M, another such pair may be chosen
with M dividing its multiplier. This uses an elementary finite argument.
The matrix

    [[f0, f0^2-1], [1, f0]]

is invertible over Z/MZ since its determinant is 1. There are at most
M^4 two-by-two matrices over this finite ring. Therefore a positive
power of this matrix is the identity. For example (M^4)! is a multiple
of its order. Let n be that positive exponent and put

    f1=chi_f0(n), j1=j0*psi_f0(n).

Then M divides j1 and

    f1^2=1+Delta*j1^2*c^4.

All new quantities are positive. The factorial is only a convenient
witness bound in this proof; it does not occur in any final polynomial.
This argument is formalizable by finite arithmetic inside ZFC.

## 5. Completeness for both fourteen-variable equations

A finite refutation gives canonical outer source coordinates with

    A=tau^2, c=psi_(a+2)(R), R=3 mod4,
    N1=Nk=Nt=1.

For P14r apply Section 4 with M=tau, choose j1 divisible by tau,
and set i=j1/tau. For P14d apply it with M=A and set i=j1/A.
In either case the new definitions give

    f=f1, Q=(Delta*j1*c^2)^2.

The auxiliary pair must be chosen fresh for this strong pair. Put
S=Delta*j1*c^2. The integer-polynomial identities in Section 4 of the
retained P66 proof give

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Vstar=-c mod f1^2, Vstar=-R mod c,
    f1^2=1 mod c, gcd(f1,c)=1.

The quotient Vstar is integral because R is odd. The stronger residue
statement uses R=3 modulo 4, which is retained from the canonical source.
It follows that

    Tstar=(Vstar+c+R*f1^2)/(c*f1^2)

is a positive integer. It satisfies
Vstar=f1^2*(c*Tstar-R)-c and the auxiliary Pell equation. Set T=Tstar
and t=tau*ystar. Equation (2) and hence the new final equation follow.

This is a canonical existence map from a finite refutation. It does not
claim that an arbitrary pre-existing multiplier is divisible by tau or A,
or that its private T,y coordinates stay fixed after powering.

Together with soundness and the retained exact P66/native/refutation
calibration, this proves in ordinary mathematics formalizable in ZFC

    no positive zero of P14r or P14d  iff  Con(ZFC).

There is no consistency assumption in this biconditional. The package
provides no new encoded ZFC proof term or end-to-end Lean/Rocq certificate.

## 6. Exact degrees after fixing the coefficient tuple

Give each quantified coordinate degree one and fixed ports degree zero.
Write

    Q0=beta*J, k0=eta+zeta,
    e0=w*s*Q0^4, c0=k0*s*Q0^3,
    A0=(w*s^2*k0*Q0^7)^2,
    L_t=w*(Q0-F-alpha)-z*Q0.

These are the appropriate top homogeneous parts. The inherited identity

    N1=2*a*c*(X+gamma*H)+(X+gamma*H)^2-H*c^2

shows that N1 has degree 18 and leader 8*gamma*e0^2*c0.
Nk has leader -h*e0 and Nt has leader L_t.

For P14r the degrees of W,Q,V,Eprod,Ns are 56,68,8,106,56. The final
nonzero degree-189 leader is

    -24*gamma*h*i^4*A0^3*e0^9*c0^11*f^4*T^2*L_t.

The monomial

    J^112*w^15*s^32*eta^17*i^4*f^4*T^2*gamma*h*z

has coefficient +24*beta^112.

For P14d the degrees of W,Q,V,Eprod,Ns are 78,14,8,52,78. The final
nonzero degree-157 leader is

    -24*gamma*h*i^2*A0^3*e0^7*c0^7*f^6*T^2*L_t.

The monomial

    J^92*w^13*s^26*eta^13*i^2*f^6*T^2*gamma*h*z

has coefficient +24*beta^92. Both coefficients are nonzero for the
actual beta>0, so these are exact degrees, not only formal upper bounds.
The degree-433 thirteen-variable equation is proved in ROOT_ANCHOR_PROOF.md.
