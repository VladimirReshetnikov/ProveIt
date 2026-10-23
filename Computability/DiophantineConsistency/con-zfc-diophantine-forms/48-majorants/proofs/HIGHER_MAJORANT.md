# A polynomial square-root majorant with an explicit separation gap

This is a replacement for the final majorant in package45's nine-variable
ratio construction. It keeps all nine variables and all source/ratio
conditions. It uses no division in the final polynomial.

## 1. Polynomial definitions

Keep the ratio construction's positive A,C,D,E,F,G,H,I,i,J,P,R, where

    J=4A-5, D=(A^2-1)C^2+1, E=iJDC^2,
    F=(A^2-1)E^2+1,
    G=A+F(CD+1-A), I=(G^2-1)H^2+1.

Put

    e=iJC, L=CD+1-A, Nstar=2G+L,
    N1=2e^2 D(D-1)L+3C,
    N2=2e^2(D-1)L,
    N3=2e^2(L-C),
    N4=2e^2 C,
    correction=256i(e^2+2)+2048,
    T=e[(1024D^2-512D-128)Nstar-64N1-40N2-28N3-21N4]
      +correction,
    Bgap=2P(P+R)+1,
    V=TH+Bgap,
    lambda=2048.

All these are ordinary polynomial abbreviations. In particular N1,...,N4
are the displayed polynomial expressions; no division computes them.
The notation N1,...,N4 here is local to this note, not the old source bounds.

For all A>=3 and C,i>=1, one has

    T > lambda*sqrt(DF)*G.

Consequently, for H>=1 with I=(G^2-1)H^2+1,

    V-lambda*sqrt(DFI) > P(P+R).

The ratio construction has A>=33280, so the modest stated hypothesis is automatic.

## 2. Exact identities underlying the majorant

Define X=e^2 D^3(D-1). The identities

    DF=X+D,
    G=e^2 D^2(D-1)L+CD+1=(X/D)L+CD+1

follow from E=CDe and D-1=(A^2-1)C^2. Fractions are used only in this proof.
Set

    tn=1024D^6-512D^5-128D^4-64D^3-40D^2-28D-21,
    dn=33792D^5+10560D^4+4928D^3+2464D^2+1176D+441.

Then exactly

    tn^2-1024^2 D^11(D-1)=dn.

For D>=1, tn>0: each lower power in its negative part is at most D^6,
and 512+128+64+40+28+21=793<1024. For D>1, dn>0. Therefore

    tn/D^4 > 1024 D^2 sqrt(1-1/D).

This finite polynomial identity proves the approximation; convergence of
an infinite expansion is not an extra dependency.

The exact remainders in dividing Nstar by D,D^2,D^3,D^4 are

    r1=3-A,
    r2=3CD+3-A,
    r3=2e^2(A-1)D^2+r2,
    r4=2e^2(1-A-C)D^3+2e^2(A-1)D^2+r2,
    Nstar=D^j Nj+rj (j=1,2,3,4).

Thus the polynomial part of T is exactly

    e*(tn/D^4)*Nstar
      +e[64r1/D+40r2/D^2+28r3/D^3+21r4/D^4].

## 3. Uniform sign and error bounds

Since D>=A^2>=9 and e=i(4A-5)C,

    eA/D < (9/2)i,
    eC/D < (3/2)i,
    e(A+C-1)/D <6i.

For example eA/D<4iA^2/((A^2-1)C)<=9i/2, and
 eC/D<4iA/(A^2-1)<=3i/2. These are uniform, including arbitrarily large i.

Both r2 and r3 are positive. The possibly negative terms are bounded by

    -e[64r1/D+40r2/D^2+28r3/D^3+21r4/D^4]
    <64eA/D+42e^3(A+C-1)/D+21eA/D^4
    <252i e^2+(765/2)i.

The correction 256i(e^2+2)+2048 is larger than this bound plus2048.

The elementary strict concavity inequality

    sqrt(X+D)<sqrt(X)+D/(2sqrt(X))

and the decomposition of G give

    lambda sqrt(DF)G
      <1024 eD^2 sqrt(1-1/D)*(2G+L)+lambda*v,
    v=(CD+1)/(2eD sqrt(1-1/D)).

Here v<1: sqrt(D(D-1))>D-1, e>=7C, and
(CD+1)/(e(D-1)) <=(D+1)/(7(D-1))<1.
Combining this with Section2 and the correction bound proves
T>lambda sqrt(DF)G. This also proves T>0 without inspecting the signs of
its subtraction schedule.

Because G^2 H^2-I=H^2-1>=0, multiplication by H and addition of Bgap yield

    V-lambda sqrt(DFI)>Bgap=2P(P+R)+1>P(P+R)+1.

This separation is deliberately imposed by an explicit low-degree polynomial.
It remains valid when other witnesses are arbitrarily large; no asymptotic
comparison is used for correctness.

## 4. The resulting finalizer using the existing h coordinate

Retain the ratio bridge's a0=(P^2-1)K^2+1, a1=DFI, u=JF,
v=QF+J(H-C), m, and Mdiv=Q+H. Put

    b1=lambda^2 a1,
    Omega=um,
    Theta=u(n+Mdiv)+v-Omega(2Mdiv+hV),
    Final=(Theta^2-Omega^2(a0+h^2 b1))^2
          -4Omega^4 h^2 a0 b1.

The existing n>=0 is the ninth finalizer coordinate. The same h>=1 already
occurs in K=R+1+h(P-1); it is not an additional variable.

The proof uses the existing four-root norm argument. Here are the necessary
noncollision and offset bounds explicitly. Write Bstar=P(P+R). The ratio
construction has R,N>=8 and positive w,s,h,i,j,b. Its definitions give

    U=N^2 w>=64, Y=N^2 s>=64, M=RY,
    P=2M^2 U, A=M(U+1), K=R+1+h(P-1), C>1.

In particular A>=33280, K>1, R<P, and

    sqrt(a0)<PK,
    h(P+R)-K=(h-1)(R+1)>=0,
    A^2-2P=M^2(U-1)^2>0.

Since C>1, D>A^2>2P and E>D. Consequently

    F>(2P-1)(2P)^2>2P^2>Bstar.

Also L=CD+1-A>1, so G>F>Bstar; and
I-G^2=(G^2-1)(H^2-1)>=0. These facts prove the distinct, required lower
bound

    sqrt(a0)<PK<=h Bstar<h sqrt(a1)<=h sqrt(b1).

Now suppose Final=0. If m=0, then Omega=0 and
Theta=u(n+Mdiv)+v>0, contradicting Final=Theta^4=0. Hence Omega is
nonzero. Factoring the four-root norm over the reals gives

    Theta/Omega=r0+h r1,  r0^2=a0, r1^2=b1.

The displayed noncollision bound makes this rational sum nonzero. Squaring
and rearranging therefore expresses each root rationally in terms of the
sum; rational square roots of integers are integers. Thus r0,r1 are
integers, a0 is a square, and a1 is a square because r1/lambda is a rational
square root of the integer a1.

For any signed integral roots, the explicit majorant gap gives

    hV+r0+h r1 >=h(V-sqrt(b1))-sqrt(a0)
                  >h(Bstar+1)-h Bstar=h.

Thus the integer Z=2Mdiv+hV+r0+h r1 is at least 2Mdiv+h+1. The defining
equation for Theta reads

    n+Mdiv+v/u=mZ.

Its left side is positive, hence m>0; its right side is integral, hence
u divides v. Conversely, if a0,a1 are squares, m>0, and u divides v, use
any signed integral roots and set

    n=mZ-Mdiv-v/u.

The inherited strict ratio bounds 0<v/u<Mdiv-1 and the bound on Z imply
n>=0. Substitution then gives Final=0. This proves the same existential
equivalence as the original ratio finalizer, with its already present h
coordinate and no new variables. The ratio bounds themselves, and the
source-to-ratio correspondence, remain the inherited hypotheses of that
construction.

## 5. A division-free cancellation certificate

The following identity uses only polynomials. Define

    Rnum=e[64r1 D^3+40r2 D^2+28r3 D+21r4]+correction*D^4.

Thus D^4 T=e*tn*Nstar+Rnum. Then

    D^8(T^2-lambda^2 DFG^2)
      =e^2 dn Nstar^2
       +1024^2 D^8[X L^2-4DG(CD+1)]
       +2e*tn*Nstar*Rnum+Rnum^2.                    (1)

To obtain the V difference, add the exact identity

    D^8(V^2-lambda^2 DFI)
      =H^2 D^8(T^2-lambda^2 DFG^2)
       +lambda^2 DF D^8(H^2-1)
       +D^8(2TH*Bgap+Bgap^2).                       (2)

These are finite ring identities suitable for independent expansion or a
Lean ring proof. D>0 justifies cancellation when inferring degrees; the
actual final polynomial never divides by D.

The optional `certificate=True` output in `nine_majorant.py` is a different
polynomial: it is exactly D^16 times Final. It forms

    other=E0^2-2E0 Omega hV-Omega^2 a0,
    inner8=D^8 other+Omega^2 h^2 [D^8(V^2-b1)],
    certificate=inner8^2-4D^16 Omega^4 h^2 a0 b1.

Here E0=u(n+Mdiv)+v-2Omega Mdiv. Thus inner8 is D^8 times the original
inner difference, and certificate=D^16 Final as a polynomial identity.
There is no division in either circuit. The independent verifier checks
both identities by symbolic integer polynomial expansion.

## 6. Exact total degree in the nine supplied coordinates

Use the package45 source degree parameter t=deg N and weight span W.
Its degree/leading coefficient data give

    e:10t+3, L:23t+4, G,Nstar:103t+22,
    D:20t+4, H:3t+1, P:12t+3, R:3t,
    correction:20t+7, Rnum:100t+23,
    tn:120t+24, dn:100t+20.

In (1), the four displayed summands have degree at most

    326t+70, 306t+62, 333t+72, 200t+46.

The cross term uniquely dominates; its leading coefficient is positive.
After subtracting deg D^8=160t+32, this establishes the exact degree
173t+40 of T^2-lambda^2 DFG^2. After multiplication by H^2 this becomes
179t+42.

In (2), the term 2TH*Bgap has degree180t+40. All other terms have strictly
smaller degree when t>2. Its leading form is the product of the leading
forms of 4,T,H and P^2, because the final padding is 2P(P+R)+1. Therefore

    deg(V^2-lambda^2 a1)=180t+40.

The finalizer uses Omega of degree115t+3W+31 and h of degree1. Let
E0=u(n+Mdiv)+v-2Omega Mdiv. Expanding its inner difference gives

    Theta^2-Omega^2(a0+h^2 b1)
      =E0^2-2E0 Omega hV
       +Omega^2 h^2(V^2-b1)-Omega^2 a0.

The third term uniquely dominates with degree410t+6W+104. Its square
therefore has exact degree

    820t+12W+208.

The final subtracted term 4Omega^4 h^2 a0 b1 has the same degree. Its
diagonal leading coefficient is 2^1494, whereas the squared inner term's
coefficient is 2^1496. Their difference is 3*2^1494, which is nonzero.
One can check noncancellation directly at the level of homogeneous forms.
Write a subscript 0 for the highest homogeneous part. Then

    (a0)_0=h^2(P_0)^4,
    (b1)_0=((TH)_0)^2,
    (V^2-b1)_0=4(TH)_0(P_0)^2.

The squared inner term has highest part
16(Omega_0)^4 h^4(P_0)^4((TH)_0)^2; the final subtracted term has highest
part 4(Omega_0)^4 h^4(P_0)^4((TH)_0)^2. Their difference is twelve times
the nonzero common form. This also proves noncancellation without relying
on diagonal evaluation.
The final degree is therefore exactly

    deg Final=820t+12W+208.

The doubled padding is material here: padding by only P(P+R)+1 would
cancel these two leading coefficients. No such cancellation occurs in
the frozen polynomial.

The division-free certificate has exact degree1140t+12W+272 and diagonal
leading coefficient 3*2^2038. The degree deduction subtracts
16deg D=320t+64 from this certificate degree; this is reasoning about
degrees, not a rational operation in the polynomial. The exported circuit
audit propagates a total-degree upper bound and a diagonal coefficient
modulo each of 1000003, 1000033, and 1000000007. The nonzero diagonal
coefficient proves that the upper bound is attained. Its values agree
with 3*2^2038 modulo all three primes.

For W=179, the supplied uniform source has t=25308 and the overlap source
has t=18942. The resulting primary degrees are 20,754,916 and 15,534,796,
respectively. Their primary straight-line programs have 599 and 655
operations over positive integers, or 602 and 658 after the three domain
shifts for nonnegative integers. The degree certificate adds 91 operations
and is an auxiliary checking artifact, not the primary equation.
