# Remove the T shift for both doubled bV equations

This is a code-free ordinary proposal for the unsheared and q-cube bV
branches. Replace b=c(T+alpha)-R by b=cT-R, with T still strictly
positive, and retain every other definition and the whole indexed
coefficient tuple. Early carrier divisibility excludes main Pell index3
without assuming q|Y, a decoded rank, B>=0, or positive b/V. Both signed
third auxiliary branches are then excluded, supplying the transport bound.

No new evaluator, source, equation artifact or finite endpoint is supplied.
Deleting the private addition suggests84/328 and81/560, respectively;
these are manual layout predictions, pending separate actual complete
materialization and independent verification. The maintained85/328 page
and every sealed parent stay unchanged. No application/source program,
import, compilation, rendering or Lean ran for this ordinary note.

The sealed V^2 sibling has its own proof. Its whole existence theorem is
not applied with a changed weight. The weight-independent root and folding
calculations are repeated here, followed by the additional bV argument.

## 1. Whole equations and coherent instance

The unsheared independent inputs are J,F,alpha,i,T,w,Y,n,eta,zeta>0.
For q-cube replace the independent Y by s>0 and define Y=q^3*s.
The four fixed ports beta,K0,MC,MF are the entire accepted directly
indexed BFS943 tuple, including Start0/Forbidden1 and initializer4.
Their whole native/controller calibration is retained; no individual
coefficient or source port is substituted. Every following symbol is a
polynomial abbreviation, not an additional quantified unknown:

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, mu=q^2+1,
    k=eta+zeta, c=k*Y+eta, A=mu*Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, V0=X*mu^2*Y^2,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fsq=1+4*a*F0=(1+2*a)^2,
    Q=Delta*(Fsq-1)=4*Delta^2*U^2*G,
    b=c*T-R, V=Fsq*b-c, L=b*V,
    Kpos=X*(3*c-2*X)+2.

For the unsheared chart let

    P=q^3*h, M=P*mu^2*H,
    Z=P*mu^2*[H*(n-L*B)+Kpos]
      +H*[mu^2*(h*Y-q^3*B)-P*e].

For the q-cube chart let

    M=h*mu^2*H,
    Z=h*mu^2*[H*(n-L*B)+Kpos]-H*[mu^2*B+h*e].

In either case define RG=M^2*G and the complete polynomial

    N=Q*(Z^2-RG*V^2)+(RG-Z^2).

The equation is N=0 over the stated ten positive inputs. Its proof form is

    (Q-1)*Z^2=M^2*G*(Q*V^2-1).

These are exactly the pinned complete85 and82 parent equations, with only
the displayed b definition changed. BINDING pins their entire private
T/Tp occurrence sets, b/V/L consumers, actual carrier/kernel rows and four
payloads. No changed diagram is emitted. The actual aliases are Am1=A-1,
Hp=H,Dtau=E,DpI2=a,Df=F0,Fsqr=Fsq,Dg=G,cTR=b,Bt=B,Mtot=M,Znum=Z.

## 2. Root recovery and folding before any transport sign

Positive inputs give q>=32, X>=q, mu>=1025, k>=2, c>=3, A>4,
Delta>=3, U>=c^2, E>1, Fsq>c+1, Q>1 and M>0. For every integral b,
b=0 gives V=-c; b!=0 gives |V|>=Fsq-c>1. Hence Q*V^2-1>0.

The unchanged product-square valuation argument recovers G=g^2 with
g>0: Q is a multiple of G, so Q-1 and Q*V^2-1 are both -1 modulo G.
No coprimality of M with G is required. Coprime E,F0 then give
E=tau^2,F0=f0^2,g=tau*f0. Rational adjacent-Pell descent, with its
denominator-preserving integral first coordinate, gives an integer y>0
and an integral signed carrier z=Z/M=epsilon*g*y satisfying

    Q*V^2-(Q-1)*y^2=1, epsilon in {-1,1}.

The doubled strong pair f=1+2a,I=2U*g satisfies

    f^2=Fsq, f^2-Delta*I^2=1, c^2|I, Q=(Delta*I)^2.

Its even strong index is permitted by the retained normalized contracts.
If b=0, the adjacent norm gives

    y^2-c^2=(c^2-1)/(Q-1).

Since I>=c^2 and Delta>=3, Q>=9c^4>c^2. This lies strictly between0
and1, impossible for an integer left side. Thus b!=0.

Writing D0=Delta*U^2>=243 gives

    a^2/g^2=D0*a/(1+a)>D0/2>9, hence a>3g and a>=c.

Consequently

    sign(V)=sign(b), |V|>=Fsq-c>a>3g, |V|>|b|,
    Fsq>2c, Fsq>g, y<(3/2)*|V|.

L=bV=|b|*|V| is positive, but a stronger bound than L>g is still needed.

The accepted signed all-index folding interface uses the strong/adjacent
norms, c<=I,c^2|I and V=-c modulo f. It imposes no sign on V and gives
c=psi_A(p),p>=1 odd. The first norm gives
k=2*psi_P0(n0),P0=2V0+1,n0>=1. If n0=1 then k=2,eta=zeta=1,
and c=2Y+1 lies strictly between psi_A(1)=1 and psi_A(2)=2A.
Thus n0>=2 and

    k>=8V0+4, c>kY>=k>8q^5, c>X, Kpos>0.

The positive ordinate c>=3 excludes p=1. None of this uses C,B,R,b,V
positive, native decoding, q parity, or an additive shift at T.

## 3. Exclude main index3 by early whole-carrier divisibility

The integrality of z from section2 already gives M|Z. Reducing the exact
carrier modulo H gives

    H|q^3*h*mu^2*Kpos             (unsheared),
    H|h*mu^2*Kpos                 (q-cube).

Since H=4muY(X+1)-1, gcd(H,mu^2)=1 without any parity assumption.
Both charts therefore satisfy the weaker common conclusion

    H|q^3*h*Kpos.                                      (1)

This is an early consequence of integral carrier recovery, not the later
whole-product projection or the later q-even denominator theorem.

Suppose p=3. Put c3=psi_A(3)=4A^2-1=4Delta+3, so c=c3.
If n0>=3, Pell growth gives k>=2*psi_P0(3)>32V0^2. Also
A<4muXY and mu^2Y^3>2, hence

    c3<64mu^2X^2Y^2<32X^2mu^4Y^5=32V0^2Y<kY<c.

This contradicts c=c3. Hence n0=2,k=8V0+4. Put u=X+2-2Y.
Expanding c=kY+eta gives the exact identity

    eta=4mu^2Y^2*(X*u+1)+8muY(X+1)+3-4Y.

The actual eta,zeta>0 imply0<eta<k. If u<=-1 then

    eta<=-4mu^2Y^2*(X-1)+8muY(X+1)+3-4Y<0,

because muY(X-1)>2(X+1), valid for muY>=3,X>5. If u>=2 then

    eta-k>=4mu^2Y^2+8muY(X+1)-4Y-1>0.

Thus u=0 or1, equivalently d=2Y-X is1 or2. In these two cases

    H=2mu(X+d)(X+1)-1.                                (2)

Moreover H is odd, 4A=5 modulo H and 4c=21 modulo H. Therefore

    4Kpos=12Xc-8X^2+8=-(X-8)(8X+1) modulo H.

Let D=(X-8)(8X+1)>0. Equation (1) gives

    H|q^3*h*D.                                        (3)

For d=1, (2) and X=wq,mu=q^2+1 give H=1 modulo q, so
gcd(H,q^3)=1. For d=2 they give H=3 modulo q, so any common prime
dividing H and q is3. If3|q the exact expansion is

    H=3+6wq+(2w^2+4)q^2+6wq^3+2w^2q^4=3 modulo9.

Thus v_3(H)=1 and gcd(H,q^3) divides3 in either case. Dividing (3)
by this gcd, and then multiplying by it, yields

    H|3*h*D.                                          (4)

But X>=q>=32 gives0<D<8X^2; (2) gives H>2q^2X^2. Consequently

    0<3hD<24qX^2<2q^2X^2<H,

contradicting (4). This proves

    p>=5 and c>c3=4Delta+3                             (5)

in BOTH charts, without q|Y, B's sign, rank p=R, q parity or source
semantics. When q|Y is literal, the shorter contradiction q|d with
d in {1,2} is available; it is not needed for the unrestricted theorem.

## 4. Exclude both signed third auxiliary branches

Put S0=Delta*I, so Q=S0^2,S0>=2. Positive Pell classification of
(S0*|V|)^2-(S0^2-1)*y^2=1 gives |V|=chi_S0(j)/S0,j>=1.
For even j the trace is +/-1 modulo S0, while S0 divides the actual
abscissa. Thus j is odd. Index1 gives |V|=1, already excluded.
Index3 would give |V|=4Q-3. The actual signed equation V=Fsq*b-c gives

    V=+(4Q-3) => Fsq*(b-4Delta)=c-c3,
    V=-(4Q-3) => Fsq*(b+4Delta)=c+c3.

By (5),0<c-c3<c+c3<2c<Fsq. Neither right side can be an integer
multiple of Fsq. This treats both signs without altering V's fixed-minus
residues. Therefore j>=5 and

    |V|>=16Q^2-20Q+5>8Q^2.

For Q>=4 the last difference is
8(Q-4)^2+44(Q-4)+53>0. Also Fsq>2c and Delta>=3 imply
Q=Delta(Fsq-1)>Fsq. The triangle inequality now gives

    |b|>(8Q^2-c)/Fsq>8Fsq-1/2>4Fsq>4g.

Together with sign(V)=sign(b) and y<(3/2)|V|, this proves the needed
pretransport majorization

    gy<(3/8)*|b||V|=(3/8)*L<L/2.                      (6)

No old b>c inequality has been reused.

## 5. Transport, late orientation and unchanged decoding

Let kappa=Kpos/H>0,rho=e/mu^2,t=B/h,W=1+hL. The new exact identity is

    e=b-cT+k-1<b, rho<b/mu^2<=|b|/mu^2,

because T>=1,c>k. It is a one-sided bound, not rho>=0. Put
sigma=Y/q^3>0 in the unsheared chart, sigma=0 in the q-cube chart.
The corresponding complete carrier gives

    n=epsilon*gy-kappa-sigma+W*t+rho.

If B<=-1 then W*t<=-L-1/h<-L. By (6),

    n<L/2-L+|b|/mu^2<0,

since mu^2>2,|V|>1 and L=|b||V|. This contradicts n>0. Hence B>=0,
and B=(K0+w)C-F,F>0 force C>0. Only now use the unchanged mask
estimates3q<R<q^4-2. Since c>8q^5>2R,T>=1, one has

    b>=c-R>0, V>=Fsq-c>0.

This does not give b>c: T=1 allows b=c-R<c. The later proof has the
following exact licenses instead:

| Later interface | Retained premises |
| --- | --- |
| Strong normalized rank | Same f,I,c^2|I,c>2p,c>2R; no b>c or T shift. |
| Signed auxiliary index | V=-c mod f and V=-R mod c, the latter from f^2=1 mod c; now V>0. |
| p=R and q even/J odd | Same normalized rank/signed-index argument; parity is obtained here, not assumed in section3. |
| Mu denominator | Integral z,L and W=1 mod h; after parity use gcd(mu^2,PH)=1 or gcd(mu^2,hH)=1. |
| First index/ratio and whole-product projection | Same A,X,Y,c,k,R and carrier denominators; T and b>c absent. |
| Remaining fractions, parity/half-binomial | Same integral kappa,rho,t and native fractions; q-cube has q^3|Y literally. |
| Native/controller and C222/ZF-to-ZFC | Reconstruct fresh unscaled source witnesses at the same entire coherent indexed instance. |

Explicitly, the unsheared denominator proof recovers mu^2|e and
H|q^3*h*Kpos; the q-cube proof gives H|h*Kpos, which implies the
weaker former premise. The later ENTIRE-product projection cancels only2
through odd H, bounds the full product and restores X=2^R and integral
kappa. It has not been replaced by cancelling selected factors separately.
The other fractions and the first-norm index then recover the complete
native arithmetic as in the accepted source. No old complete theorem
requiring positive T-alpha is applied to that possibly nonpositive value.

## 6. Both whole positive witness directions

From a positive zero of either pinned shifted bV parent, set

    T_new=T_old+alpha,

and fix every other independent input and all four fixed ports. Then
b,V,L,Z,M,N are exactly unchanged, and all new inputs are positive.
The intended private one-addition removal has this universal forward map.
Its formal inverse T_old=T_new-alpha is not claimed positive on an
arbitrary new tuple. Conversely sections2–5 decode a finite syntactic
refutation from every new positive zero; canonical predecessor witnesses
can then be rebuilt afresh if a shifted old zero is desired.

Direct canonical completeness retains the whole canonical indexed family,
including R>3q,R=3 modulo4 and, for q-cube, positive Y divisible by q^3.
Choose a fresh seed Pell period modulo c^2*tau and double its pair as in
the repaired source. Source61 section5 supplies the positive integral

    V*=chi_(Delta*I)(R)/(Delta*I),
    T*=(V*+c+R*f^2)/(c*f^2)>0.

Set new T=T*, not T*-alpha. Its b,V are the same canonical values as
the shifted predecessor. The actual R>3q family, not the insufficient
generic R=3 shifted-positive-T statement, supplies positive old T if
needed. With L=bV>0, canonical g>kappa+sigma,t>=0,rho>=0 give

    n=gy+(1+hL)*t+rho-kappa-sigma>0.

For q-cube sigma=0; equivalently use its already canonically sheared n.
Every independent input is positive and N=0. Strong, seed and auxiliary
Pell witnesses are rebuilt together, not mixed across incompatible tuples.
This proves ordinary positive-zero/refutation equivalence at the same
whole instance and hence its retained no-zero/Con(ZFC) interpretation,
without asserting either side or producing a new internal proof object.

## 7. Literal layout, entire highest forms and finite boundary

The actual unsheared85 source has T only in row47,Tp=T+alpha, and Tp
only feeds row48,cT=c*Tp. The q-cube82 source has the corresponding
rows48/49. BINDING pins all occurrences, including b's extra L=bV use.
The intended literal change removes Tp and changes only cT's operand
from Tp to T; alpha stays live through C/R. All other rows and four
payloads are intended unchanged. The manual product/sum/difference
predictions are84=(51,18,15),81=(49,18,14); no new graph census is claimed.

For unsheared c*alpha has degree3, below R's degree4, so the full
degree328 highest form is unchanged:

    -2^10*q0^156*w^34*Y^78*i^14*k0^44*(q0-F)^2.

For q-cube the leading b changes from k0*q0^3*s*(T+alpha) to
k0*q0^3*s*T. Its complete degree560 highest form becomes

    -2^10*i^14*q0^384*w^34*s^80*k0^46*T^2,
    q0=beta*J,k0=eta+zeta.

The selected coefficients -2^10*beta^156 and -2^10*beta^384 are nonzero
for the actual positive beta. The dominant final term is the same
-Q*M^2*G*V^2 product as in the two pinned bV parents. These are ordinary
global degree arguments, not acceptance of a new emitted endpoint.

A later independently reviewed source packet must materialize full
diagrams, all rows/free-port identities/coefficient bindings and live
counts, check the entire highest forms, reject meaningful actual-artifact
controls and reproduce normal/optimized results. This note supplies none
of those finite/runtime results. It does not combine weights, change the
native alphabet/controller, alter a page, or touch Lean. Partial clearings
Y=q*s or q^2*s remain separate future layout investigations with their
own carrier and positive-map obligations, not accepted numerical results.
