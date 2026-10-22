# Twelve positive unknowns by a separating weighted sum

This is a new reduction of the certified blank-input arithmetic interface.
The coefficient ports must be bound as a whole to a compiler tuple for which
that interface is proved. The proof below does not change the tile compiler.
The parent report supplies the exact coefficient binding and the inherited
signed Pell/rank and blank-tableau arguments.

The new unknowns, all strictly positive integers, are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

All subsequent named expressions are substituted integer polynomials, not
additional unknowns. `build_twelve.py` emits every binary arithmetic gate.

## 1. The retained blank-input prefix

Write the fixed ports as beta=B-1, kappa, MC, MF, with MF already shifted as
required by the blank compiler. Define

    q=beta*J+1, Cword=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y, H=4*a+3, Delta=a^2+H,
    P=X+a*c, S=1+Delta*c^2,
    L=E*k*Y, A=1+L*(L+k),
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-h*E-R,
    Nt=(kappa+w)*Cword+q-F-z*(q-1).

The inherited weak bootstrap, valid when Nk and Nt are units, gives

    q>=16, X>=16, Y>=4096, 0<R<E-2.

In particular Cword>=0, c>1, c<2*k*Y, and a+2<2*E. This bootstrap does
not use any of the four roots eliminated below. That ordering matters.

## 2. Strengthen the strong multiplier to be divisible by H

Define

    G=H*i*c^2,
    D=1+Delta*G^2,
    Q=Delta*(D-1)=(Delta*G)^2,
    d=Q-1,
    v=c*T, b=c+R*D,
    e=Q*(D*v^2+b^2)-1, Baux=2*Q*v*b.

The four roots to be eliminated satisfy

    (P+H*gamma)^2=S,
    tau^2=A,
    f^2=D,
    d*y^2=e-Baux*f.

Equivalently the last equation is

    Q*(v*f-b)^2-(Q-1)*y^2=1.

The H in G ensures gcd(H,d)=1 because Q is divisible by H^2. This is the
integrality device: it will separate the possible denominators of gamma
and y after all roots have first been proved rational.

Requiring the normalized strong multiplier to be H*i loses no accepting
blank witnesses. Here is the precise modification of the canonical
completeness witness. Put Aparam=a+2, and define the Pell polynomials by

    chi_Aparam(n)+psi_Aparam(n)*sqrt(Delta)
      =(Aparam+sqrt(Delta))^n.

The canonical witness has c=psi_Aparam(R) and R=3 modulo four. The matrix

    [[Aparam,Delta],[1,Aparam]]

has determinant one and therefore a positive period modulo H*c^2.
Choose m to be an arbitrarily large common multiple of R and that period
(and, harmlessly, of c*R). Then

    i=psi_Aparam(m)/(H*c^2)>0, f=chi_Aparam(m),
    rho=Delta*psi_Aparam(m), Q=rho^2,
    Vaux=chi_rho(R)/rho, y=psi_rho(R).

The quotient Vaux is integral because R is odd. For an odd n, the
polynomial chi_z(n)/z is a polynomial in z^2; at z^2=1-Aparam^2 it
equals (-1)^((n-1)/2)*psi_Aparam(n), and its constant term is
(-1)^((n-1)/2)*n. Hence R=3 modulo four and
rho^2=Delta*(f^2-1) give

    Vaux=-c modulo f, Vaux=-R modulo c.

Also f^2=1 modulo c and gcd(f,c)=1. It follows that

    o=(Vaux+c)/f, T=(o+R*f)/c

are positive integers: the first congruence proves integrality of o,
and multiplying the second numerator by the unit f modulo c proves
integrality of T. Then Vaux=c*(T*f-1)-R*f^2 and the ordinary Pell norm
of chi_rho(R),psi_rho(R) gives the required auxiliary equation. All
other canonical blank-witness coordinates are unchanged. Thus there
is no circular requirement on m or an implicit divisibility assumption.
The parent report supplies the precise inherited canonical-witness
and Pell-polynomial references.

## 3. Two separating weights

Set

    W0=H^2*i^2*c^3,
    M=1+8*T*H*i*c^2+16*R*E*W0,
    N=1+2*H*M.

The retained unknown t will represent

    t=y+M*tau+N*gamma.

Notice gcd(N,H)=1. Also N does not need a separate large polynomial
bound: the main radicand S exceeds the first radicand A.

Here are the needed quantitative bounds, including all complex branches
of the auxiliary square root. Put

    Fcap=(a+2)*G, Ycap=2*(v*Fcap+b).

Since G>1 and Delta=(a+2)^2-1, sqrt(D)<Fcap. Since Q>=2,

    |y|^2 <= [Q*(v*sqrt(D)+b)^2+1]/(Q-1)
           <= 2*(v*sqrt(D)+b)^2+1 < 4*(v*sqrt(D)+b)^2 < Ycap^2.

The inequalities use the complex absolute value and therefore also
cover a nonreal auxiliary branch. Here v*sqrt(D)+b>1. Further
sqrt(A)>L>E*c/2. Since Fcap<2*E*G and D<4*E^2*G^2,

    Ycap < 4*c*T*E*G+2*c+8*R*E^2*G^2.

Consequently

    |y|/sqrt(A)
      < 8*T*H*i*c^2+4/E+16*R*E*H^2*i^2*c^3 < M,

because E>=q^4>=16^4>4.

To prove S>A, observe c>k*Y and Delta-E^2>2*E*Y. Thus

    Delta*c^2 > k^2*Y^2*Delta
              > k^2*(E^2*Y^2+E*Y)=A-1.

It follows that

    N*sqrt(S)/H > 2*M*sqrt(S)
                > 2*M*sqrt(A) > M*sqrt(A)+|y|.

These are strict bounds on every branch. They prove that the map

    (gamma,tau,f,y) -> y+M*tau+N*gamma

is injective on its algebraic solution set. Indeed, if gamma differs,
its contribution has magnitude 2*N*sqrt(S)/H and dominates the possible
differences in the other two displayed terms. If gamma is the same
but tau differs, the difference 2*M*sqrt(A) dominates |y1-y2|.
If gamma and tau agree and the displayed values agree, then y agrees;
the linear equation d*y^2=e-Baux*f and Baux>0 force f to agree too.

## 4. An explicitly computed polynomial, with no quantified roots

Let W=H*t+N*P, m=H*M. In the four-dimensional algebra with formal
generators r and u satisfying r^2=A and u^2=S, form

    F(r,u)={d*(W-m*r-N*u)^2-H^2*e}^2-H^4*Baux^2*D.

Reduce this expression uniquely to f0+f1*r+f2*u+f3*r*u. Then put

    U=f0^2+A*f1^2-S*(f2^2+A*f3^2),
    V=2*(f0*f1-S*f2*f3),
    Norm12=U^2-A*V^2.

This is simply two quadratic norms. The following scalar formulas make
clear that the definition contains only addition, subtraction, and
multiplication, and no hidden unknowns or division:

    a0=d*(W^2+m^2*A+N^2*S)-H^2*e,
    a1=-2*d*W*m, a2=-2*d*W*N, a3=2*d*m*N,
    f0=a0^2+A*a1^2+S*a2^2+A*S*a3^2-H^4*Baux^2*D,
    f1=2*(a0*a1+S*a2*a3),
    f2=2*(a0*a2+A*a1*a3),
    f3=2*(a0*a3+a1*a2).

The emitted circuit uses positive versions of -f1 and -f2 to save
unnecessary negation gates; their squared norm is identical.

The proposed three-equation system is

    Nk=1, Nt=1, Norm12=0.

The proposed single polynomial equation is

    Polynomial12 = Nk*Nt*(1+Norm12)-1 = 0.

Its four coefficient ports are fixed integers, once bound to the compiler.

## 5. Rationality, then integrality

The norm has the exact factorization over an algebraic closure

    Norm12=d^8*H^16* product [t-y-M*tau-N*gamma],

where the product runs over the sixteen branches of the four root
equations, with algebraic multiplicity. Therefore Norm12=0 at integer
inputs implies that at least one algebraic tuple has the specified
integer value t. All polynomial coefficients are rational. Every
automorphism of a finite normal closure over Q sends this tuple to a
tuple with the same t. Injectivity from Section 3 forces the entire
tuple to be fixed. Hence gamma,tau,f,y are rational.

Now tau^2=A, f^2=D, and (P+H*gamma)^2=S show that tau, f, and
u=P+H*gamma are integers: a rational number with an integer square is
an integer. The reduced denominator of gamma therefore divides H.
If y=r/s in lowest terms, d*y^2=e-Baux*f implies s^2 divides d.
The denominators of gamma and y are consequently coprime.

But N*gamma+y=t-M*tau is an integer, and gcd(N,H)=1. Thus neither
denominator can cancel against the other, and both are 1. All four
recovered roots are integers. This step is the reason for the H-divisible
strong multiplier; rationality alone would not establish the result.

The reconstructed gamma can have either sign. The inherited signed
ordinary theorem permits gamma,tau,f,y,T to be signed, while retaining
the positive compiler coordinates. If desired, tau and y may be replaced
by their absolute values. Neither is zero: A>1, and y=0 would give
Q*(v*f-b)^2=1 with Q>1. Replacing f,T by -f,-T preserves every equation.
The ordinary strong multiplier is i_ordinary=Delta*H*i, because

    (i_ordinary*c^2)^2=Delta*(f^2-1)=Q.

Thus the recovered tuple falls exactly under the signed parent theorem.

For the product equation, all three factors are integer units. Since
V is even, Norm12 is a square modulo four. Therefore 1+Norm12 cannot
be -1: it equals 1, so Norm12=0 and Nk*Nt=1. The weak bootstrap and
the preceding reconstruction allow both common signs of Nk,Nt. The
inherited signed rank argument subsequently forces both signs to be
positive and recovers the blank accepting tableau. This ordering avoids
assuming the desired signs before reconstructing the roots.

Conversely take an accepting blank tableau, use the strengthened strong
multiplier from Section 2, and take the canonical positive roots. Then
t=y+M*tau+N*gamma is a positive integer, and one factor in the norm
vanishes. Both the system and the single equation therefore have a
positive solution. Combining with the inherited machine endpoint proves
the desired ZFC equivalence after negating witness existence.

## 6. Exact degree and arithmetic cost

Every supplied unknown has degree one. The relevant degrees are

    c:5, E,a,H:6, Delta:12, R:4, A,S:22,
    G:17, D:46, Q,d:58, b:50, M:39, N:45.

Norm12 has degree 16 in t and exact total degree 1360. Polynomial12
has exact total degree 1369. These are degrees of the substituted
polynomials, not just of expressions with auxiliary registers.

Here is a uniform leading-form certificate. Scale all twelve unknowns by
a formal parameter lambda, keeping the four coefficient ports fixed.
Subscript top denotes the leading homogeneous part. Then

    A_top=S_top=E_top^2*c_top^2,
    b_top=R_top*Delta_top*H_top^2*i^2*c_top^4,
    M*sqrt(A) has leading term +/-16*b_top of degree 50.

The two gamma roots have orders 5 and -1. This follows directly from

    H^2*gamma^2+2*H*P*gamma+(P^2-S)=0,
    P^2-S=X^2+2*X*a*c-H*c^2-1,

whose three coefficient degrees are 12, 17, and 16. The large root has
leading term -2*P_top/H_top, and N*gamma then has leading term
-64*b_top of degree 50. The small root contributes only degree 44.
Each auxiliary y branch has leading term +/-b_top of degree 50;
the two f branches have identical leading y magnitudes.

Consequently the sixteen factors in Section 5 have leading multiples
of b_top with magnitudes

    15,17,15,17,15,17,15,17,
    47,49,79,81,47,49,79,81.

No leading term vanishes. Their product is

    C0=15^4*17^4*(47*49*79*81)^2.

Thus

    (Norm12)_1360=C0*d_top^8*H_top^16*b_top^16,
    1360=8*58+16*6+16*50.

All factors are nonzero polynomials for every valid compiler binding:
in particular beta>0 and R_top=(beta*J)^3*(beta*J-F) is nonzero.
Nk and Nt have nonzero leading forms of degrees 7 and 2 respectively,
which proves the degree 1369 for the product.

The fully charged live DAGs contain:

| Construction | Unknowns | Equations | Degree | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|---:|---:|---:|
| System, comparisons free | 12 | 3 | 1360 | 95 | 45 | 140 |
| Residual system, outputs equal zero | 12 | 3 | 1360 | 95 | 47 | 142 |
| Product | 12 | 1 | 1369 | 97 | 47 | 144 |
| Sum of squares | 12 | 1 | 2720 | 98 | 49 | 147 |

Every multiplication by a fixed numeral is charged. Assignment, reuse,
and the final comparisons are free, matching the collection's convention.
The residual form computes Nk-1 and Nt-1 explicitly and therefore uses
two additional subtractions. The sum of squares is
(Nk-1)^2+(Nt-1)^2+Norm12^2. Constants are the four fixed compiler ports and
displayed fixed integers. The gate count is not a claim of circuit optimality.

## 7. Reproducibility

Run

    python3 build_twelve.py --degree

The command emits the complete live systems and polynomial and checks:

* 24 independent integer evaluations of the gate DAG against a separate
  direct quadratic-norm implementation;
* the two coprimality identities and the modulo-four guard;
* an exact nonzero synthetic witness with H=3, d=8, e=224, Baux=108,
  D=4, A=9, S=25, P=2, M=100, N=10000, and t=10301;
* exact modular univariate degrees and the predicted leading coefficient.

The synthetic witness is a fixture for the elimination algebra, not a
solution of the complete K215 equation. The modular specialization is a
supplementary certificate; the leading-form proof above establishes the
uniform exact degrees. No K215 halting run is claimed or used. The new
proof is ordinary mathematics formalizable in ZFC, not a new Lean or Rocq
kernel certificate.
