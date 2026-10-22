# Independent mathematical audit of the twelve-variable norm reduction

Reviewed against `proofs/TWELVE_VARIABLE_PROOF.md` and
`code/build_twelve.py`. This is a mathematical review, not a new proof-assistant
certificate. The finite compiler has been independently handled separately.

## Result

The proposed twelve-positive-variable system and product polynomial pass the
following independent checks of their new mathematical steps. In particular,
the proof separates rationality from integrality and does not silently lose
the denominator condition on the auxiliary Pell root. The system uses the
ordinary signed parent theorem with positive original multiplier
`i_old=Delta*H*i`. A direct source for that theorem is
`11-t4/reduction/SIGNED_DOMAIN_PROOF.md`, whose nine positive ports match the
recovered tuple. Package 14's top-level odd-i/square-w theorem should not be
cited as if those additional specializations were hypotheses of the current
construction; only its general soundness argument is relevant here.

## 1. Weak bootstrap precedes root extraction

Assume the two retained factors Nk,Nt are units. With the authentic four
coefficient ports, beta=B-1>0, 0<MC<beta, beta<MF_source<2beta, and K>1.
For C=q-F-alpha, Nt=(K+w)C+q-F-z(q-1). If C<0 then q-F=C+alpha<=q-1,
and z>=1 gives Nt<=-(K+w)<-1, a contradiction. More explicitly the bound
q-F<=q-1 follows from F>=1 independently of C. Thus C>=0 and
q-F=C+alpha>=1. Consequently alpha<=q-F<=q-1 and

    q <= (q-1)(q-F)+alpha <= q(q-1).

Since J=(q-1)/beta, the upper mask term is

    (MC+q MF_source)J < (1+2q)(q-1).

It follows that

    q(q^2-1) < R < q^4-q^3+q^2-1 < q^4-2.

With X=wq, Y=sq^3 and E=XY, all the advertised bounds hold:
q>=16, X>=16, Y>=4096, E>=q^4>R+2, c>kY, c<2kY,
and a+2<2E. These deductions use no eliminated root and are therefore
valid before the Galois/separating-trace argument.

## 2. Separation inequalities, including complex y branches

Let G=Hic^2, D=1+Delta G^2, Q=Delta(D-1), d=Q-1,
v=cT, b=c+RD. All are positive, and Q>1. The values tau and
u=P+H gamma are real because their squares A,S are positive. The
possible f values are real with |f|=sqrt(D); y may be real or imaginary.

Because Delta=(a+2)^2-1 and G>1,

    sqrt(D)<(a+2)G=Fcap.

From d y^2=Q(Dv^2+b^2)-1-2Qvb f, complex absolute values give

    |y|^2 <= [Q(v sqrt(D)+b)^2+1]/(Q-1)
           <=2(v sqrt(D)+b)^2+1
           <4(v sqrt(D)+b)^2 < [2(v Fcap+b)]^2.

Thus the stated Ycap is a valid bound on every branch. Since
sqrt(A)>L=EkY>Ec/2, a+2<2E, and D<4E^2G^2, division yields

    |y|/sqrt(A) < 8TG+4/E+16RE G^2/c
                  < 1+8THic^2+16REH^2i^2c^3 = M.

Also S>A: c>kY and Delta>E^2+2EY imply
Delta c^2>k^2(E^2Y^2+EY)=A-1. For N=1+2HM,

    N sqrt(S)/H > 2M sqrt(S) > M sqrt(A)+|y|.

If two root tuples have the same trace t=y+M tau+N gamma, different
gamma values differ by 2sqrt(S)/H and the N-weighted contribution
strictly dominates the maximum difference of the other two terms.
With gamma fixed, different tau values differ by 2sqrt(A), and M times
that difference strictly exceeds the maximum y difference. Finally, equal
gamma,tau and trace give equal y; the nonzero coefficient Baux=2Qvb then
forces equal f. Thus the trace is injective even when y is imaginary.

## 3. The norm is exactly the product over branches

Let r^2=A and u^2=S, and set W=Ht+NP and m=HM. The auxiliary equation
is equivalent to

    d(W-mr-Nu)^2-H^2 e = -H^2 Baux f.

Taking the f-norm gives

    F(r,u)=[d(W-mr-Nu)^2-H^2 e]^2-H^4 Baux^2 D.

Reduce F to f0+f1r+f2u+f3ru. Taking the u-norm yields U+Vr with

    U=f0^2+A f1^2-S(f2^2+A f3^2),
    V=2(f0f1-S f2f3).

Taking the r-norm gives U^2-A V^2, as in the code. Each F has leading
coefficient d^2H^4 in t and degree 4, so the full norm has leading
coefficient d^8H^16 and factors over all sixteen root branches as stated.
Repeated roots only contribute algebraic multiplicity and do not affect
the existence or automorphism argument. The code's simultaneous sign
reversal of f1,f2 reverses V but leaves the norm unchanged.

In particular Norm12=0 implies a branch with trace t. A finite normal
closure over Q contains that branch. Every automorphism preserves both
the rational defining equations and the integer trace t. Injectivity
therefore fixes the whole branch pointwise, proving its four coordinates
are rational. This step does not by itself claim integrality.

## 4. The denominator argument is valid and necessary

Rational tau,f,u with integer squares are integers. Thus the reduced
denominator a_gamma of gamma=(u-P)/H divides H. If y=r/s in lowest
terms, d y^2=e-Baux f with an integer right side implies s^2|d.
Since Q=(Delta Hic^2)^2, d=Q-1 is coprime to H. Hence
gcd(a_gamma,s)=1. Moreover N=1+2HM is coprime to H, so multiplying
gamma by N does not remove its denominator. The equation
N gamma+y=t-M tau in Z now forces both coprime denominators to be 1.
All four roots are integers. There is no unhandled rational root.

## 5. Projection to the signed parent theorem

Set i_old=Delta H i>0. Then

    (i_old c^2)^2=Delta(f^2-1)=Q.

The reconstructed auxiliary expression V_aux=vf-b equals
c(Tf-1)-Rf^2 exactly, and the extracted equation is
Q V_aux^2-(Q-1)y^2=1. The main and first Pell norms are also exact.
This is the original ordinary-strong core with its nine required positive
coordinates and six allowed signed coordinates. The signed rank theorem
applies to |f| and the absolute main root; it recovers the actual rank
p=R before resolving the two possible unit signs. No positivity of gamma
or f was used prematurely. The parent theorem then proves the tableau
and K215 halt conclusions. For the single polynomial, V in the outer
norm is even, so Norm12 is a square modulo 4. Thus the integer unit
1+Norm12 cannot be -1; it is 1 and Norm12=0. The only remaining unit
ambiguity is Nk=Nt=+1 or Nk=Nt=-1, which the cited signed theorem handles.

## 6. Full strengthened completeness argument

Start with a canonical positive blank-tableau witness at the final actual
rank R. Its original main Pell parameter is A_pell=a+2, discriminant
Delta=A_pell^2-1, and c=psi_Apell(R), with R=3 modulo4. Consider the
integer matrix

    U = [[A_pell,Delta],[1,A_pell]], det(U)=1.

Modulo Hc^2 this matrix belongs to a finite group, so some positive
power U^ell is the identity. Choose m any positive common multiple of
ell and R. The standard matrix formula gives

    U^m=[[chi(m),Delta psi(m)],[psi(m),chi(m)]],

so Hc^2 divides psi(m). Therefore take

    f=chi(m)>0, i=psi(m)/(Hc^2)>0,
    I=Delta psi(m)=Delta Hic^2.

This gives f^2=D and I^2=Q. The auxiliary index m need not be odd.
Let r=(R-1)/2, which is odd, and define the integer quotient polynomial
Q_r by chi_Z(2r+1)=Z Q_r(Z^2). Put

    V_aux=Q_r(I^2)=chi_I(R)/I>0, y=psi_I(R)>0.

The identities Q_r(1-A_pell^2)=-psi_Apell(R)=-c and Q_r(0)=-R give

    V_aux=-c (mod f), V_aux=-R (mod c),

because I^2=Delta(f^2-1) and c divides I. Thus o=(V_aux+c)/f is a
positive integer. Since f^2=1 modulo c,
of+R=0 modulo c implies o+Rf=0 modulo c. Hence

    T=(o+Rf)/c>0

is an integer, and c(Tf-1)-Rf^2=of-c=V_aux, restoring the exact
compressed auxiliary expression. All original nonauxiliary variables,
including gamma and tau, retain their canonical positive values. Finally
t=y+M tau+N gamma is a positive integer and one norm factor vanishes.
This proves completeness of the H-divisible strong specialization.

## 7. Degree certificate spot check

The stated exact leading-form proof is consistent. At generic simultaneous
scaling, A_top=S_top=E_top^2 c_top^2. The auxiliary root has leading
term +/-b_top, M tau has leading term +/-16b_top. The two gamma branches
have orders 5 and -1 because the coefficients of the quadratic in gamma
have degrees 12,17,16. The large branch gives N gamma=-64b_top at
degree50; the small branch contributes only degree44. Therefore the
sixteen factor coefficients have the stated nonzero magnitudes
15,17 (each four times) and 47,49,79,81 (each twice). The norm degree is
8*58+16*6+16*50=1360. Multiplication by Nk and Nt adds 7+2, giving
exact degree1369. This is a tradeoff in degree and circuit size for the
new twelve-variable count, not dominance of the prior13-variable form
under every metric.
