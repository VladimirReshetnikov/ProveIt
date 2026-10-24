# Direct positive base with the zero-offset main parameter

This separate ordinary endpoint combines the accepted direct-base carrier
and accepted zero-offset Pell parameter. Its ten inputs are strictly
positive integers J,F,alpha,i,T,x,Y,n,eta,zeta. The same four coherent
fixed ports satisfy beta odd,beta>=31,K0>0 and0<MC<beta<MF<2beta.
All earlier packets, pages and Lean files remain unchanged. No new
Lean or internal-ZFC endpoint is asserted.

## 1. Complete definitions and the independent base domain

Use the direct-carrier definitions

    q=beta*J+1, X=q+x, mu=q²+1, a=Y(X+1), A=mu*a+1,
    k=eta+zeta, c=kY+eta, I=i*c², Delta=A²-1,
    C=q-F-alpha, B=(q*K0+X)C-qF,
    H=4A-5, b=c(T+alpha)-R, L=HI+b,
    W=1+q(q-1)L, P=q⁴(q-1), M=P*mu²*H,
    Kpos=X(3c-2X)+2, e=k-R-1,
    Z=P*mu²[H(n+V)+Kpos]
       +H[mu²(q(q-1)Y-q³WB-(q-1)X)-P*e].

The unchanged R, first norm, strong/auxiliary kernels and weighted
three-root norm are the complete literal definitions in equation.json.
In particular V=Df*b-c, Df=Delta*I²+1, Q=Delta²*I²,
delta=Q-1 and Dnum=Q*V²-1. The scalar equation is the same weighted
octic norm of the four arguments

    delta*Z²; 9*delta*M²*Dtau, delta*M²*Df, M²*Dnum.

Its exact rational center is

    Z/M=n+V+Kpos/H+Y/q³-WB/[q(q-1)]-X/q⁴-e/mu².       (1)

Rational expressions are proof notation; evaluation uses only integer
addition, subtraction and multiplication. Initially only X=q+x>q>=32
is known. There is no initial w coordinate, no q|X premise and no
assumed integer X/q. Literal a is omitted by sharing the existing
muY: mu*(XY+Y)=(muY)*(X+1). This is a universal polynomial identity,
and changes no zero-offset polynomial value.

## 2. Zero-offset estimates apply before any q divisibility

The accepted zero-offset ratio lemma is uniform in X>=32,Y>=1 and
lambda>=1. With a=Y(X+1), A=lambda*a+1 and
P0=2Xlambda²Y²+1 it gives, for r>=1,

    xi < psi_A(2r+1)/psi_P0(r+1)
       < xi*(1+1/a)^(2r), xi=(X+1)^(2r)/X^r.          (2)

Its proof uses the universal P4 estimate, the exact lower-margin
identity and A<=lambda(a+1). It does not use X=wq. The bound with
1/a also implies the older weaker bound with3/a wherever needed.

Here lambda=mu>=1025 and X>q>=32. The accepted zero-offset
unconditional bounds A>4,A>Y and Delta>V0+1, where
V0=Xmu²Y², use only these inequalities. The adjacent-radicand bounds
and cleared-modulus noncancellation therefore recover the same positive
integral roots tau,f,y. Modulo mu the normalized radicands still have
residues(-9,-1,-1), with the same pair/triple obstructions. No center
sign, q|X conclusion or primitive-denominator cancellation is used.

The uniform strong/auxiliary folding lemma at A>=3 gives
c=psi_A(p) for odd p>=1. The first norm gives
k=2psi_(2V0+1)(n0). If n0=1, c=2Y+1 lies strictly between
psi_A(1)=1 and psi_A(2)=2A, impossible. Thus n0>=2 and

    c>kY>=k>=4(2V0+1)>8Xmu²Y².                       (3)

In particular c>2X and Kpos>0 before transport or projection.
Exactly as in the zero-offset proof,

    4tau<(A-1)I, f<AI, hence3tau+f<(2A-1)I.

Also A=muY(X+1)+1>X+2 and I>=1, so

    X/q⁴<X<(2A-4)I, hence3tau+f+X/q⁴<HI.             (4)

These estimates use X>=q, never q|X. The same kernel bounds give
b>0,V>0,0<y-V<b/2 and |e/mu²|<b/2 while e/mu² is still rational.

## 3. Transport sign, rank and parity precede denominators

The signed-root center relation from(1) reads

    n=eps1*3tau+eps2*f+(eps3*y-V)-Kpos/H-Y/q³
        +WB/[q(q-1)]+X/q⁴+e/mu².

If B<=-1, then W=1+q(q-1)L gives WB/[q(q-1)]<-L.
Together with(4), the two b/2 bounds and Kpos/H,Y/q³>0,
this makes n<HI+b-L=0, contradicting n>0. Thus B>=0.
Since qK0+X>0 and qF>0, its definition forces C>0. The unchanged
mask bounds now give3q<R<q⁴-2.

The normalized strong rank and signed auxiliary-index argument are
uniform at the new A. The same c²|I,c>2R,c>2p and congruences give
p=R before denominator cancellation. Odd p makes R odd and the
same mask parity proof then gives q even. None of these steps defines
w or divides X by q.

Only now use gcd(mu²,q⁴(q-1)H)=1. The q-even calculation licenses
the q-1 factor, while H=-1 modulo mu and gcd(mu,q)=1 handle the
others. Every other fraction in(1) has denominator dividing
q⁴(q-1)H. Separating the single modulus mu² gives mu²|e.
No pairwise coprimality of the different q powers is asserted.

The first-index argument also survives the new A because

    2V0+1-A=muY(2muXY-X-1)>0.

The unchanged first Pell congruence, mu²|4V0 and mu²>q⁴ therefore
give n0=(R+1)/2 in their original chronology. Put R=2r+1. Then
r>=48. Applying(2) gives Y>X^r/3 and

    X^(r+1)<3a<H.                                      (5)

No whole-product or q-divisibility conclusion has been used to
license the first-index or ratio steps.

## 4. Whole-product projection with the direct carrier

The integral signed center implies H|P*Kpos, P=q⁴(q-1).
The universal identity Kpos=HXc-2Kquad, with
Kquad=X[X+2(A-2)c]-1 and H odd, gives H|P*Kquad by cancelling
only2. The uniform projection lemma at the new A,H makes H divide

    P*(X-2^R)*(2^R*X+1).                              (6)

For X>=q>=32 and r>=35,

    X^(r-1)>=q^5*32^(r-6)=q^5*2^(5r-30)
            >q^5*2^(4r+4)=q^5*2^(2R+2).

Our r>=48 satisfies this. Each factor in the absolute value of
(X-2^R)(2^R X+1) is less than2^(R+1)X. Since P<q^5,
its complete product in(6) has absolute value strictly below
X^(r+1)<H. Thus it vanishes and X=2^R; the other factor is positive.
P is not cancelled through H. Only after this vanishing does the
uniform projection give H|Kquad and H|Kpos directly, so Kpos/H
becomes an integer.

## 5. Recover q|X and all remaining source data late

With e/mu² and Kpos/H integral, (1) gives

    Y/q³-WB/[q(q-1)]-X/q⁴ is an integer.

Its numerator q(q-1)Y-q³WB-(q-1)X is a multiple of q⁴(q-1).
Reduction modulo q proves q|X. The H denominator has already been
removed in section4, so H is not illicitly cancelled modulo q.

As X=2^R, q=2^kappa for kappa>=5. The bound4kappa<=2^kappa=q,
together with R>3q, gives R>4kappa and therefore q⁴|X. Thus
u=X/q⁴ is a positive integer. Only now put w=X/q>0. Then

    B=q*Bt, Bt=(K0+w)C-F, B/[q(q-1)]=Bt/(q-1).

Remove the integer u from the preceding rational relation. The
coprimality of q³ and q-1 gives q³|Y and q-1|W*Bt; W=1 modulo
q-1 gives q-1|Bt. The quotient t=Bt/(q-1)>=0 follows from B>=0.
The fixed-minus parity and half-binomial rounding arguments use the
same X,Y,R and the zero-offset bound(2), which is stronger than
their accepted3/a upper estimate. They recover the same source data.

The unscaled source reconstruction uses its prescribed A_source=a+2,
not the present scaled A. Its w and z=1+t are the integers just
recovered. The retained uniform source61/native/controller theorem
then gives a finite refutation, including the allowed J=1 case.
This proves soundness for the complete coherent original tuple and,
separately, the coherent BFS tuple. Their different K0 numerals are
not identified or individually interchanged.

## 6. Completeness from the accepted 99 zero-offset zero

A finite refutation supplies a positive zero of the accepted99/368
zero-offset equation by its fresh canonical completeness proof.
Its soundness licenses X=2^R,q=2^kappa,R>3q,q⁴|X and the integer
t=Bt/(q-1)>=0. In particular X>q. Keep all its inputs except w,n
and put x=X-q>0. Both equations now have exactly the same X, new
zero-offset A, all kernels, roots, b,L,R and Kpos. No old107 scaled
witness is being reused.

Let W99=1+(q-1)L and Wnew=1+q(q-1)L. Their difference is
DeltaW=(q-1)²L>0. Put

    n_new=n99+DeltaW*t+X/q⁴.

This is a positive integer even when t=0. Since B=qBt, the exact
normalized centers agree. More explicitly the full integer numerator
identity is

    Znew-qZ99
      =Hmu²[q⁴DeltaW((q-1)t-Bt)+(q-1)(q⁴u-X)],
      u=X/q⁴.

Both residuals vanish. Thus Znew=qZ99 and Mnew=qM99. Every norm
argument scales by q² and the full norm output scales by q^8. The
new equation therefore vanishes, without choosing a particular
signed root factor. A positive pointwise inverse n map is not claimed.

## 7. Literal count, full coefficients and exact degree

The direct107 parent loses only its private E,a,a2 definitions;
insert Xp1=X+1 and move existing muY before Am1=muY*Xp1. The
universal identity mu*(XY+Y)=(muY)*(X+1) binds the whole shared
zero-offset polynomial. The final graph has105 live operations:
63 multiplications,24 additions,18 subtractions. All ten strictly
positive inputs and all four complete fixed payloads are unchanged.

The direct base degree remains1 and its high-degree front forms
are unchanged by removing the lower-degree offset2mu. The complete
front bounds are A4,Delta8,I5,Df18,Q26,V22,L9,W11,P5,M13,Z35.
After the exact Z=MV+Z0 cancellation, Z0 has degree24; the omega
terms have degree bounds74,85,70,26, with the unique degree85 term
2Q0*Z00*M0*V00. The full centered norm uniquely has top omega^4
of degree340.

With q0=beta*J and X0=q0+x its full omega leading form is

    2^7*q0^39*X0^9*i^5*Y^19*(eta+zeta)^10
       *B0*(q0-F),
    B0=(q0*K0+X0)*(q0-F-alpha)-q0*F.

The highest x exponent is10; its fourth power gives the nonzero
coefficient2^28*beta^156 at
J^156*x^40*i^20*Y^76*eta^40*alpha^4*F^4, of total degree340.
The complete literal row map, norm coefficients, leading forms,
all fixed payloads and signed/rational carrier identities are checked
independently. Finite controls supplement these universal algebraic
identities and the unbounded ordinary proof; they do not replace them.
