# Removing a quotient by using the auxiliary Pell ordinate as its residue certificate

## Result and comparison boundary

This note constructs three fixed polynomial equations in fourteen strictly
positive integer variables. Their respective pairs (binary operations, exact
total degree) are (66,174), (67,158), and (68,146). All four fixed coefficients
are the unchanged, coherent Start-only4127 tuple of ProveIt package 174 at
commit `02a78a08603cbae248c19c23a75907c6c6bd6443`. The tuple occupies 97,046
raw bytes. No coefficient port is borrowed from another native encoding.

The immediate parent is package 174's fifteen-positive-variable P66 of degree
157. The mechanism is a new composition of its normalized auxiliary ordinate
with the residue-carrier method already proved for combined roots in package
170. The residue-carrier lemma itself is credited to package 170; this note
does not claim worldwide novelty. The resulting fourteen-variable equations
have different evaluation graphs and lower operation counts than that
package's thirteen-variable constructions. In particular the first and third
new profiles dominate the documented fourteen-positive-variable 70/189 and
71/157 profiles, respectively, when comparing just domain, variable count,
operation count, and degree. Their coherent coefficient tuples differ, and no
same-polynomial claim is made.

All arguments below are ordinary integer arithmetic formalizable in ZFC.
The new proof restores an exact P66 zero, so the identified native/refutation
calibration is inherited. There is no new end-to-end Lean/Rocq certificate.

## 1. Literal polynomials

The fourteen independent variables, all strictly positive, are

    J,F,alpha,z,f,n,i,T,s,w,tau,eta,zeta,gamma.

Let beta,K0,MC,MF be the whole supplied fixed tuple. As in the parent,
beta>=31 is odd, K0>0, and 0<MC<beta<MF<2beta. Define

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3,
    E=X*Y, k=eta+zeta, ell=E*k*Y, c=k*Y+eta,
    a=E+Y, H=4*a+3, Delta=a^2+H=(a+2)^2-1,
    D=X+a*c+gamma*H,
    R=[(q-1)*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    V=f^2*(c*T-R)-c,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Nt=(K0+w)*C+(q-F)-z*(q-1).

For the first equation put M=E and d=E; for the second and third put
M=q^4 and d=q^2. The relation M|d^2 holds in both choices. Define

    u=k-M*n-R, I=d*i*c^2, S=Delta*I,
    Na=S^2*(V^2-u^2)+u^2,
    Ns_scaled=Delta*f^2-S^2,
    Ns=f^2-Delta*I^2.

The equations are

    P_E = N0*N1*Na*Nt*Ns_scaled - Delta = 0,
    P_q = N0*N1*Na*Nt*Ns_scaled - Delta = 0,
    P_q_direct = N0*N1*Na*Nt*Ns - 1 = 0,

where the first uses (M,d)=(E,E), and the other two use
(M,d)=(q^4,q^2). All definitions are polynomial abbreviations and introduce no
extra quantified unknown. In particular M and d are the displayed fixed
polynomials, not extra variables. The signed carrier u replaces the old
positive y only inside its square. Its sign is deliberately unrestricted.

The identity P_q=Delta*P_q_direct holds as an integer polynomial. Since
Delta>0 on the positive domain, these last two equations have exactly the
same positive zero set. The third uses one additional multiplication to
compute S*I=Delta*I^2; this removes the extraneous factor Delta and lowers
degree by twelve without changing the quantified variables.

## 2. Unit signs and noncircular outer bounds

At a positive zero, Delta>0. Dividing the first two displayed equations by
Delta is proof notation only. All three reduce to

    N0*N1*Na*Nt*Ns=1.                                      (2.1)

Every factor is therefore +1 or -1. We now determine each sign without
using the omitted quotient or any index authentication.

Write v=XY^2=EY. Then N0=tau^2-v(v+1)k^2. Since v>=2, the negative
Pell equation x^2-v(v+1)y^2=-1 has no integer solution. Here is a direct
descent proof. For a solution choose |y| minimal and replace x,y by their
absolute values. Then vy<x<(v+1)y, because
x^2-v^2y^2=vy^2-1>0. Multiplication by the norm-one unit
(2v+1)-2*sqrt(v(v+1)) produces another integer solution with ordinate

    y'=abs((2v+1)y-2x),

and 0<y'<y. The ordinate cannot be zero because its norm is -1. This
contradicts minimality. Thus N0=1.

Because Delta=(a+2)^2-1 is 0 or 3 modulo 4, neither N1 nor Ns can be -1.
Since S^2 is 0 or 1 modulo 4, Na is congruent to u^2 or V^2 modulo 4,
so Na cannot be -1 either. Equation (2.1) therefore yields

    N0=N1=Na=Ns=Nt=1.                                      (2.2)

Deleting the old Nk factor is useful here: Nt has no unresolved partner
sign. In particular

    (K0+w)C = 1+z(q-1)-(q-F) >= F > 0,

so C>0. These bounds are established before recovering the main index.
Let G0=(q-1)(q-F)+alpha=q*alpha+(q-1)C. Positive F,alpha,C imply

    q<=G0<=q(q-1),
    0<(MC+q*MF)J<(2q+1)(q-1).

The lower mask bound uses MF>beta and beta J=q-1. The resulting retained
mask estimate is

    3q<R<q^4-q^3+q^2-1<q^4-2<=E-2.                       (2.3)

Consequently R<M for either choice of M. No division by E and no old h
has been used in this argument.

## 3. Recovering the main Pell index before the quotient

For b>=2 let chi_b and psi_b be the Pell sequences given by

    chi_b(0)=1, chi_b(1)=b,
    psi_b(0)=0, psi_b(1)=1,
    U(j+2)=2*b*U(j+1)-U(j).

Use the standard Pell classification, addition and composition identities,
strict monotonicity, and strong divisibility. These are the same ordinary
lemmas as the retained package-170 proof. We include the precise index
argument so that its independence of h is explicit.

Put A=a+2 and P0=1+2v. From N0=1,

    tau=chi_P0(r), k=2*psi_P0(r), r>=1.                    (3.1)

The fundamental positive solution of x^2-v(v+1)y^2=1 is (2v+1,2):
y=1 would require a square strictly between v^2 and (v+1)^2, and y=2
gives that displayed solution. N1=1 gives

    D=chi_A(p), c=psi_A(p), p>=1.                          (3.2)

If r=1 then k=2, eta=zeta=1, and c=2Y+1 lies strictly between
psi_A(1)=1 and psi_A(2)=2A. Hence r>=2 and

    k>=8XY^2+4, c>kY>8XY^3>2R.                           (3.3)

Also P0>A. Monotonicity, c>k, and (3.1)--(3.2) give r<p. Since p>=3
and A>=2, the recurrence then gives c=psi_A(p)>2p.
The strong norm Ns=1 gives

    f=chi_A(m), I=psi_A(m), m>=1,

and c^2|I holds by the literal definition of I. Strong divisibility first
gives p|m. Write m=pj. The composition identity gives
I=c*psi_D(j). Modulo c one has D^2=1 and
psi_D(j)=j*D^(j-1). Since D is a unit modulo c, c^2|I implies c|j.
Consequently

    pc|m, c|m, m>2p.                                    (3.4)

Now Q=S^2=Delta*(f^2-1)>1, and Na=1 becomes

    QV^2-(Q-1)u^2=1.                                    (3.5)

Neither u nor V is zero. In fact (2.3), (3.3), and f^2>2 imply
V=f^2(cT-R)-c>0. Pell classification at base S gives

    SV=chi_S(nu), abs(u)=psi_S(nu)

for an odd positive nu: even-index chi values are +1 or -1 modulo S,
whereas SV is divisible by S.

For nu=2j+1 define integer polynomials L_j by

    L_0(Z)=1, L_1(Z)=4Z-3,
    L_(j+1)(Z)=(4Z-2)*L_j(Z)-L_(j-1)(Z).

The recurrence identities are

    chi_b(2j+1)=b*L_j(b^2), L_j(0)=(-1)^j*(2j+1),
    L_j(1-A^2)=(-1)^j*psi_A(2j+1).

Use Q=1-A^2 modulo f and V=-c modulo f. This gives
psi_A(nu)=+c or -c modulo f. Squaring and using
chi_A(2t)=1+2*Delta*psi_A(t)^2 gives

    chi_A(2nu)=chi_A(2p) modulo chi_A(m).

The signed step-down lemma says that for 0<j<m such a congruence with
chi_A(j) forces its index to be +j or -j modulo 2m. To verify it, reduce
and reflect with the addition identities to a signed chi_A(s), 0<=s<=m.
The endpoint s=m has residue zero; a negative representative cannot
equal the specified positive one because 2chi_A(m-1)<chi_A(m); and
strict monotonicity identifies the positive representative. Applying
the lemma with j=2p<m gives nu=+p or -p modulo m, hence modulo c.

Separately Q=0 modulo c and V=-R modulo c give nu=+R or -R modulo c.
Thus p=+R or -R modulo c. Since 0<p,R<c/2, the equality is

    p=R.                                                 (3.6)

This is the main index authentication. The omitted quotient is still absent.

## 4. The auxiliary ordinate carries the missing residue

Both choices of M satisfy M|v. Also M|S^2 because M|d^2.
Reducing the first Pell recurrence at P0=1 modulo M gives

    k=2r modulo M.                                       (4.1)

For every j>=0 the odd Pell ordinate satisfies

    psi_S(2j+1)=(-1)^j modulo 4S^2.                      (4.2)

This follows by induction from the recurrence, or from the even-power
polynomial for an odd ordinate. Equations (3.5) and (4.2), with either
sign of u, therefore give u=+1 or -1 modulo M. The literal carrier
u=k-Mn-R yields

    2r-R=epsilon modulo M, epsilon in {1,-1}.             (4.3)

From r<p=R and R<M, one has abs(2r-R-epsilon)<R<M.
Thus the congruence is the integer equality 2r=R+epsilon.

The case epsilon=-1, namely R=2r+1, is impossible. Put B0=2A^2-1>P0.
Composition and monotonicity give

    c=psi_A(2r+1)>psi_A(2r)
      =2A*psi_B0(r)>=2A*psi_P0(r)=A*k>k(Y+1),

contradicting c=kY+eta<k(Y+1). Hence

    2r=R+1.                                              (4.4)

The full recurrence at P0=1+2v gives k=2r modulo 4v. Therefore

    h_old=(k-R-1)/E

is an integer. It is positive by k>=8XY^2+4 and R<q^4-2<=E-2.
Set i_old=d*i and y_old=abs(u)>0. All remaining coordinates are retained.
The restored tuple is an exact positive zero of the original P66 equation:
the old Nk is +1, and its N0,N1,Na,Nt,normalized strong norm are all +1.
Thus every new positive zero gives a finite syntactic ZFC refutation through
the unchanged P66 whole-tuple calibration.

## 5. Constructive completeness with fresh private Pell witnesses

Conversely a finite syntactic refutation supplies canonical outer witnesses
from the Start-only4127 native/P66 calibration. In particular R=3 modulo 4,
c=psi_A(R), k=2psi_P0((R+1)/2), and the old quotient, first norm, main
norm and transport factors are all +1.

Choose a positive period of the determinant-one Pell matrix at base A
modulo c^2*d. The finite group of invertible matrices modulo this positive
integer gives a positive index m with c^2*d|psi_A(m). Put

    f=chi_A(m), i=psi_A(m)/(c^2*d), I=d*i*c^2, S=Delta*I.

Every quantity is positive and f^2-Delta*I^2=1. This choice is made before
choosing auxiliary witnesses. Define fresh

    V_star=chi_S(R)/S, y_star=psi_S(R).

Because R is odd, V_star is integral; both quantities are positive.
The polynomial identities from Section 3, now used modulo f^2 and c,
give

    V_star=-c modulo f^2, V_star=-R modulo c.

Here S^2=1-A^2 modulo f^2, c|S, and (R-1)/2 is odd. Also
gcd(c,f)=1 and f^2=1 modulo c. Consequently

    T=(V_star+c+R*f^2)/(c*f^2)

is a positive integer, and V_star=f^2(cT-R)-c.

Since M|S^2 and R=3 modulo 4, equation (4.2) gives y_star=-1 modulo M.
The first Pell recurrence and 2r=R+1 give k-R=1 modulo M. Therefore

    n=(y_star+k-R)/M

is a positive integer. It makes the literal carrier u=-y_star, whose
square has the required value. All new independent coordinates are
strictly positive, all unit factors are +1, and the new polynomial is zero.
No old auxiliary ordinate or strong multiplier is silently held fixed.

Combining Sections 4 and 5 establishes, in ZFC, positive zero existence
if and only if a finite syntactic ZFC refutation exists. Negation gives

    ZFC proves: (no positive zero of P) iff Con(ZFC).

No consistency assumption selects the coefficients or enters the proof.

## 6. Exact arithmetic costs and degrees

The first new graph reuses the parent's three gates for k-hE-R as the
carrier k-nE-R and feeds its square to the auxiliary norm. Removing Nk
from the final product saves one multiplication. Scaling S by E costs one
multiplication. Thus there are still 66 live binary operations, but only
fourteen quantified positive variables. The smaller-modulus graph replaces
that scaling by q^2 and adds one gate for q^4, giving 67 operations. The
unscaled strong norm uses one further multiplication, giving 68.

For exact degrees write q0=beta*J, k0=eta+zeta, and
B0=w*(q0-F-alpha)-z*q0. The complete highest homogeneous components are

    [P_E]_174 = 8*q0^103*gamma*i^4*k0^13*w^16*s^29*T^2*f^4*B0,
    [P_q]_158 = 8*q0^95*gamma*i^4*k0^13*w^12*s^25*T^2*f^4*B0,
    [P_q_direct]_146 = 8*q0^87*gamma*i^4*k0^13*w^10*s^23*T^2*f^4*B0.

The main norm has cancellation from apparent degree 22 to exact degree 18:
with Z=X+gamma*H,

    N1=2*a*c*Z+Z^2-H*c^2.

No subsequent leading cancellation occurs. In the two scaled graphs the
factor degrees N0,N1,Na,Nt,Ns_scaled are respectively
(22,18,74,2,58) and (22,18,66,2,50). The direct graph replaces the last
degree 50 by 38. These sum to 174, 158, and 146.

Taking the term -z*q0 from B0 and eta^13 from k0^13 gives attained
coefficients -8*beta^104, -8*beta^96, and -8*beta^88. Since beta>0,
the degrees hold at the actual fixed coefficients, not just generic ports.

The literal graphs, liveness checks, independently recomputed leading
forms, source identities, and coherent coefficient bindings accompany this
proof. Finite tests authenticate these artifacts; they do not replace the
unbounded Pell and native/refutation arguments.

## 7. Scope and further questions

The three positive-domain equations are ordinary polynomials. Their unchanged
expressions are not asserted to have the same equivalence on wholly
unrestricted integer inputs. The separate INTEGER_DOMAIN.md proves that
f,tau,n may range over all integers, and explicitly converts the other eleven
coordinates using 1+a^2+b^2+c(c+1). Applied to the degree-146 equation this
gives the supplied polynomial in 36 unrestricted integers, with exact degree
288 and 145 binary operations. It is a domain conversion justified by a
specific sign audit, not a new 14-integer-variable theorem.

Further research can ask whether the same shared ordinate can carry a
second omitted quotient without another free coordinate, whether stronger
index bounds permit a modulus below q^4, and whether a root-elimination
version of this normalized construction improves the thirteen-variable
arithmetic frontier. Each would need a fresh noncircular soundness proof.

Inherited sources: package 174 `compact66/preferred4127/start_only_polynomial.json`
and `compact66/calibration/P66_POSITIVE_PROOF.md`; package 170
`report/compact_proof.tex`, especially its signed index and residue-carrier
proofs. All pinned to the commit named above. The new proof uses the actual
calibrated whole tuple, not merely the displayed inequalities on its ports.
