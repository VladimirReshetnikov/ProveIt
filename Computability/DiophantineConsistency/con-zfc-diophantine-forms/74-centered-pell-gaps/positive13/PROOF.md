# Adaptive second carrier: thirteen positive variables in degree 30

This is an ordinary existence-preserving reduction of package 61 at
ProveIt commit `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`. The complete
compact44 coefficient tuple and package61's precise compiler/calibration
interface are inherited. No new proof-assistant certification is asserted.
The new literal polynomial has thirteen strictly positive unknowns, degree
30, and 93 live binary arithmetic gates. Package61's corresponding point
has degree 34 and the same 93 gates.

## Complete formula

The only unknowns are

    j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma > 0.

The fixed integer ports are the *whole* compact44 tuple
`beta,K0,MC,MF`, with `beta=2^590069-1`; `MF` is already shifted.
Define polynomial abbreviations

    J=3j+1, q=beta J+1, C=q-F-alpha,
    E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, b0=X+ac, I=ic^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    r0=k-R-1, L=qY, U=qL=q^2Y,
    Dstar=U b0+H(U gamma+L X-r0),
    Kaux=Delta(f^2-1), V=f^2(cT-R)-c,
    W=(q-1)k+1, M=q^3(q-1),
    Bt=(qK0+X)C-qF,
    Z=M(ell+k+r)+(q-1)Y-q^3 W Bt.

In `Bt`, `qF` means multiplication of q and the supplied F.
The residuals and output polynomial are

    A0=Z^2-M^2[ell(ell+k)+1],
    A1=Dstar^2-U^2(1+Delta c^2),
    Aa=(V+u)^2-Kaux*u*(2V+u)-1,
    As=f^2-Delta I^2-1,
    P13=A0^2+A1^2+Aa^2+As^2.

The sole change from source61 is the replacement

    U=q^5, L=q^4   -->   U=q^2Y, L=qY.

The named abbreviations do not add existentially quantified variables.

## Ordered soundness argument

Since the polynomial is a sum of squares, a positive zero makes all four
residuals zero. Rational-square-root integrality applied to A0 first gives
`M|Z`. Reduction modulo q^3 gives `q^3|Y`; reduction modulo q-1 gives
`q-1|Bt`, because W is 1 modulo q-1. Put `s=Y/q^3>0` and
`t=Bt/(q-1)`. The proof-only integer `tau=Z/M` satisfies

    tau^2=ell(ell+k)+1,
    tau=ell+k+r+s-Wt.

The first identity gives `|tau|<ell+k`, so `Wt>r+s>0`, and hence
`Bt>0`. But `C<=0` would imply `Bt=(qK0+X)C-qF<0`. Therefore C>0.
The authentic compact44 masks now give the inherited estimates

    q>=16,    3q<R<q^4-2.

No q-divisibility of X was used. Since 590069 is odd, beta is 1 modulo
three, and J is 1 modulo three, hence `q=2 (mod 3)`. Moreover
`H=4Y(X+1)+3=3 (mod q)`, because q^3 divides Y, and thus
`gcd(q,H)=1`.

The numerator Dstar is positive before any index recovery. Indeed
`r0<k`, `c>kY`, and `U>=q^5`, so

    Dstar > Uac-Hk > k(UaY-H) > 0.

The final strict inequality follows from q>=16, Y>=q^3 and H=4a+3.
From A1=0, rational-square-root integrality gives a positive integer
`D=Dstar/U`, with

    D^2-Delta c^2=1,
    U | H(LX-r0).                                    (1)

The source61 Pell arguments can now be used unchanged: with A=a+2 and
P0=2XY^2+1, there are p,n0>=1 with

    c=psi_A(p), D=chi_A(p),
    k=2 psi_P0(n0), |tau|=chi_P0(n0).

The case n0=1 would force k=2, eta=zeta=1 and c=2Y+1, contradicting
`c>=psi_A(2)=2A>=4Y+4`. Therefore n0>=2, and

    c>kY>8XY^3>=8q^9>2R,    n0<p,    c>2p.

From As=0 and c^2|I, the normalized rank lemma gives f=chi_A(m),
I=psi_A(m), c|m, and m>2p. The auxiliary equation Aa=0 is

    (Delta I)^2 V^2-((Delta I)^2-1)|V+u|^2=1.

The congruences `V=-c (mod f)` and `V=-R (mod c)` and the preceding
bounds meet every hypothesis of the signed index lemma in source61,
giving **p=R**. This step does not use a restored transport/index quotient
or q|X.

### The possible common divisor three

One must not simply cancel H modulo U. Put

    g=gcd(H,U)=gcd(H,Y)=gcd(3,Y) in {1,3}.

The equalities use gcd(q,H)=1 and H=4Y(X+1)+3. Define

    mu=L/g=qY/g.

Because g divides Y and is coprime to q, q^3 divides Y/g; consequently
**mu>=q^4**. Equation (1), after cancelling exactly g, implies
`U/g | LX-r0`. Since mu divides U/g and LX, we obtain `mu|r0`.

The first-Pell congruence is `k=2n0 (mod 4XY^2)`. The modulus mu divides
4XY^2: indeed `4XY^2/mu=4XYg/q` is an integer. Thus

    mu | 2n0-R-1.

Since `1<=n0<p=R<q^4<=mu`, the absolute value of this last integer is
strictly smaller than mu. Hence `2n0=R+1`. It follows that

    r0=k-2n0

is a positive multiple of 4XY^2. In particular U divides r0, since
`4XY^2/U=4XY/q^2` is integral. Equation (1) therefore gives U|HLX.
Using U=qL and cancelling the positive integer L yields q|HX. Finally
gcd(q,H)=1 gives **q|X**. Define the recovered positive integers

    w=X/q,   h=r0/E,   gamma_old=gamma+w-r0/U.

The first two are positive integers. The last is integral and satisfies
`D=X+ac+H gamma_old`. Since D>(a+1)c and c>kY>X, gamma_old is positive.

Now `Bt=q[(K0+w)C-F]`; the already proved q-1|Bt and Bt>0 give a positive
integer z_new satisfying `(K0+w)C-F=(q-1)z_new`. Set z_old=z_new+1.
This restores the inherited transport condition. Set Told=fT, and restore
the positive roots |tau| and |V+u|. Every positive witness of source61's
normalized kernel has now been recovered. Its named native/compiler
calibration therefore gives a finite syntactic ZFC refutation.

## Completeness

Start with the canonical compact44 witness supplied for a finite
refutation. Source61 proves J=1 modulo 3, J>1, X=2^R, w=X/q>q,
Y=sq^3, R=3 modulo 4, n0=(R+1)/2, gamma_old>w, and
r0 a positive multiple of 4XY^2. Hence U divides r0 and

    gamma=gamma_old-w+r0/U > 0

is an integer. It makes Dstar=UD and A1=0. The source61 choices

    j=(J-1)/3,
    t=q(z_old-1),
    r=Wt+tau-ell-k-s

remain positive and give A0=0. Reselect the source61 canonical auxiliary
pair and its positive T,u; this gives Aa=As=0 without affecting either
carrier. Thus every finite syntactic refutation supplies a positive zero.
Negating the two existence implications yields, by ordinary mathematics
formalizable in ZFC, the requested equivalence with Con(ZFC).

## Exact degree and operation count

Put q0=3 beta j, k0=eta+zeta, and

    R0=q0^3(q0-F),
    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F.

The highest homogeneous forms of the residuals are

    in_15(A0)=-2 q0^8 k0^2 X Y^2 Bt0,
    in_13(A1)=8 q0^2 k0 X^2 Y^4 (q0^2 Y gamma+R0),
    in_13(Aa)=2 X^2 Y^2 f^4 u R0,
    in_14(As)=-i^2 k0^4 X^2 Y^6.

They are checked by exact polynomial arithmetic in `check13.py`. Only
A0^2 reaches degree 30, so

    in_30(P13)=4 q0^16 k0^4 X^2 Y^4 Bt0^2.

For example, the coefficient of
`j^16 eta^4 X^4 Y^4 alpha^2` is `4(3 beta)^16>0`, even after
specializing the actual fixed ports. Thus degree 30 is exact, not a
generic-coefficient upper bound. The literal circuit has 93 live gates:
52 multiplications, 24 additions, and 17 subtractions. All multiplication
by numerals and every squaring are counted; constant leaves and reuse
are free. The count concerns this evaluator and does not prove minimality.

The finite checker establishes transcription, polynomial identities,
degree, liveness and count. It does not prove the unbounded compiler or
calibration theorem and does not search for a consistency witness.
