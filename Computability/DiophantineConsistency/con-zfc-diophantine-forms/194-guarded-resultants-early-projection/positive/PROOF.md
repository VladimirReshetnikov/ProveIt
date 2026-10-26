# Quotient centers and early projection in the free ten-positive chart

## Result, domain, and attribution

This package gives three ordinary polynomials in exactly ten independently
quantified **strictly positive integer** variables:

| Graph prefix | Operations | Exact degree | Transport | Root scale |
|---|---:|---:|---|---:|
| quotient_t | 97 | 202 | bV | 2 |
| product2 | 111 | 198 | bV | 2 |
| product4 | 119 | 190 | b² | 4 |

Every graph is supplied at two separate complete native/refutation
calibrations: historical indexed943/radix67 and current low-padding2963.
The latter has 69,685 raw coefficient bytes, not the frozen4177 tuple's
98,219 bytes. Each of its four integers, native proof, exact942-selector
bijection, physical marker and Pclp controller changes as one coherent unit.
No coefficient port, old word or controller certificate is transferred alone.

The free chart Y=s, lambda=q, inverse-Lucas correction and unsquared trace
are credited to source172, whose full retained parent is `parent/`.
Source178 supplies the A-quotient idea and the full-product Omega4 evaluator;
its original proof and algebra are retained in `inherited/`. Those incoming
scaled-chart profiles 96/220 and116/208 do not improve the prior free-chart
90/206. Our contributions are the compatible free-chart composition, the
cheaper t=A−1 quotient, first-product truncation, and early p=3 projector
exclusion which newly licenses square transport here. The last step avoids
illicitly importing the scaled-chart q|Y argument.

All binary +,−,* gates, squares and scalar products are charged. Fixed
integer leaves and reuse are free. These are measured tradeoffs, not a global
optimality or literature-priority claim. Ordinary soundness/completeness,
composed with the identified retained syntactic calibration, proves in ZFC:

    The equation has no positive-integer zero iff Con(ZFC).

No consistency decision, actual zero, unsolvability assertion, new compiled
formal-kernel replay or new encoded internal-ZFC proof object is claimed.
Finite algebra and byte checks do not prove the unbounded lemmas by testing.

## 1. The complete ordinary polynomials

The independent variables in graph order are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

Fix the entire chosen tuple beta,K0,MC,MF. Both actual tuples satisfy
beta>=73 odd, K0>0 and 0<MC<beta<MF<2beta. The strengthened beta bound is
used explicitly in section3; no theorem for arbitrary beta>=31 is asserted.
MF is the source mask with beta added exactly once, not the native mask.
Define these polynomial abbreviations, none a new quantified variable:

    h=beta J, q=h+1, C=q−F−alpha, X=qw, Y=s, Ybar=qY,
    k=eta+zeta, c=kY+eta,
    A=Ybar(X+1)+1, Delta=A²−1, H=4A−5,
    v=X Ybar², ell=vk, E=1+ell(ell+k),
    R=[h(q−F)+alpha](q²−1)+(MC+qMF)J,
    B=(K0+w)C−F, U=ic², a=Delta U²E, F0=1+a,
    G=EF0, f=a+F0, Q=4Delta aF0,
    b=cT−R, V=fb−c, K=X(3c−2X)+2,
    e6=6(k−R−1)−ell(k²−4), D=6q⁷, M=hDH.

Choose a row below; the formulas are division-free integer polynomials.
For quotient_t put

    Qt=(kYbar)[ell+k−(kYbar)Ybar],
    C2=U(2AE−Qt), Omega=C2 V, r=2, L=bV.

For product2 put

    S=(kYbar)[ell+k−(kYbar)(Ybar+1)], theta=U²b,
    Omega=U{2A[EV−theta(E²+S²)]
                  +S[4theta E−(b−c)]}, r=2, L=bV.

For product4 put

    S=(kYbar)[ell+k−(kYbar)(Ybar+1)], theta=U²b,
    e2=(kYbar)², Rc=theta(3E+e2)−(b−c),
    Sc=4E²+3S²+e2²,
    Omega=U[2S Rc+A(4EV−theta Sc)], r=4, L=b².

In every case set

    Z0=hD[H(n−LB)+K]−H[DB+h(e6−6q⁴s)],
    Z=Z0−M Omega,
    P=Q(Z²−r²M²GV²)+(r²M²G−Z²).                 (1)

The single equation is P=0. No rational constant, division, recurrence,
radical, floor, variable exponent, hidden witness or oracle is a graph gate.
The quotient_t implementation shares V in n−V(bB+C2) and computes
2A=(A−1)+(A+1) using two already-live registers.

For proof only put t0=B/h, kappa=K/H, rho=(e6/6)/q⁷,
sigma=Y/q³, W=1+hL and z=Z/M. Before integrality is established these are
rational quantities. Identically,

    z=n+kappa+sigma−Wt0−rho−Omega,
    P=(Q−1)Z²−r²M²G(QV²−1).                    (2)

## 2. Root extraction before sign or denominator assumptions

At every positive input q>=74, X>=q, Y>=1, c>=3, A>q², H>0,
U>=c², f>2c and Q>c². The exact identities

    f²−1=4aF0, Q=Delta(f²−1)=4Delta²U²G,
    gcd(E,F0)=1, f−1=2Delta i²c⁴E

are unchanged from the retained parent. V cannot vanish. If P=0, the
integer equation(2), valuations at primes dividing G, and the square
factor r² show that G is a square. Thus E=tau², F0=f0² and g=tau f0>0.
The parent's rational adjacent-Pell descent, unchanged by the constant
square scale, gives y=|z|/(rg) an integer and

    QV²−(Q−1)y²=1, z=epsilon rgy, epsilon=±1.

In particular z is integral. The signed all-index folding theorem applies
with I=2Ug, f²−Delta I²=1, Q=(Delta I)² and c²|I. It gives
c=psi_A(p) for p positive odd; c>=3 excludes p=1. Hence

    p>=3, c>=c3=4Delta+3>4q⁴, K>0.

All of this is independent of the signs of R,B,C,b,V. No q|Y,
authentication p=R, auxiliary-index-three exclusion or large-rank ratio
bound has been used.

The first square gives k=2psi_(1+2v)(m), m>=1. m=1 gives k=2,
eta=zeta=1 and c=2Y+1 strictly between the first two main ordinates,
so m>=2. The first base 1+2v>A, and c>k. Strict base/index monotonicity
therefore gives m<p: if m>=p, psi_(1+2v)(m)>psi_A(p)=c, impossible.
This m<p fact does NOT use p=R or any mask bound.

## 3. New early projector exclusion of main index three

Integrality of z already gives H|Z. Reducing the literal numerator(1)
modulo H gives H|hDK. Since D=6q⁷ and gcd(H,q)=1,

    H | 6hK.                                      (3)

The shift M Omega and either transport are multiples of H; they do not
change this step. We retain the entire factor6h.

Suppose p=3. Then m=2 by section2. Write u=X+2−2Y. Using
c=4A²−1, k=8Xq²Y²+4, eta=c−kY gives the exact polynomial identity

    eta=4q²Y²(Xu+1)+8qY(X+1)−4Y+3.              (4)

If u<=−1, the first term is at most −4q²Y²(X−1). Since qY>=32,
X>=32, we have qY(X−1)>2(X+1)+1, so(4) is negative.
If u>=2, subtracting k from(4) leaves at least
4q²Y²+8qY(X+1)−4Y−1>0. Both alternatives contradict 0<eta<k.
Thus u is0 or1, so 2Y=X+2 or X+1 and

    H=4qY(X+1)−1>2qX².                           (5)

For p=3 the projector is the direct identity

    4K+(X−8)(8X+1)=3XH(4A+5).                   (6)

Together(3),(6) show H divides the positive integer
N=6(q−1)(X−8)(8X+1). Because X>=32,
0<N<48qX². By(5), j=N/H is an integer with1<=j<=23.
Modulo q, H≡−1, X≡0 and N≡48, so j≡−48 modq.
But49<=j+48<=71<q, impossible. Therefore p>=5 and c>c3.
This is a universal proof at the explicitly verified beta>=73 boundary;
finite tests of small inputs are not its justification.

Now b cannot vanish by the adjacent-square gap argument from the parent.
It has the sign of V. The auxiliary Pell index is odd and at least3.
At index3 its two signs would give respectively

    f(b−4Delta f)=c−c3,
    f(b+4Delta f)=c+c3.

Both right sides lie strictly between0 and2c<f, impossible. Thus that
index is at least5, and

    |V|>=16Q²−20Q+5>8Q²,
    |b|>8f³−1/2>7f³, f>6g,
    y<3|V|/2, |V|<3f|b|/2.                     (7)

This finally licenses square transport. The proof did not silently exclude
an index-three branch before its required early projector argument.
For the two bV rows the weaker inherited bound |b|>4Delta f−1
would already suffice: Delta>=4 and f>6g imply
4Delta f−1>96g−1>72g for integer g>=1. their validity does not depend on square transport.

## 4. Centers are small, with both signs covered

Let C0=AUE. Since G=E+Delta U²E²,

    0<C0<3g/2.                                  (8)

For quotient_t set Rt=1+k²Ybar²(Ybar²−1)>0. Exact polynomial division
by t=A−1 gives E=(A−1)Qt+Rt. Also
Qt=k²Ybar[(X−1)Ybar²+1]>0, hence Qt<E/(A−1).
Consequently 0<C2=U(2AE−Qt)<2AUE. Thus Omega has the sign of V and

    2gy+|Omega|<3g|V|+3g|V|=6g|V|<L/2.         (9)

For the product rows, temporarily regard A as an indeterminate T over
Z[Ybar,k,U,b,c]. Then

    E(T)=e2 T²+e1 T+e0,
    e2=k²Ybar²,
    e1=k²Ybar(1−2Ybar−2Ybar²),
    e0=1+k²Ybar(Ybar+1)[Ybar(Ybar+1)−1],
    V(T)=(1+2(T²−1)U²E(T))b−c, F(T)=E(T)V(T).

Let Qj be the value at A of the polynomial quotient of F(T) by T^j.
Then exactly

    Omega2=U(2AF−Q1),
    Omega4=U(4AF−2Q1−Q3/2).                     (10)

Q3 is coefficientwise even, because the only odd-coefficient candidate
(b−c)E has T-degree at most2. Equations(10) are proof-only descriptions;
the literal evaluators in section1 use no quotient or division gate.

For a polynomial, superscript# denotes absolute-coefficient evaluation
at A. Put delta=(Ybar+1)/A<1/16. The coefficient bounds
|e1|<2e2(Ybar+1), 0<e0<=e2(Ybar+1)² give E#(A)<2E. Since
c+1<2U²E and |V|>(f−c)|b|>Delta U²E|b|,

    F#(A)<2E(|b|+c)+8(A²+1)U²E²|b|,
    F#(A)/|EV|<8+20/Delta<10.

Deletion of low coefficients gives |Qj|<=F#(A)/A^j. As A>=16,

    |Omega2−2AUEV|<AUE|V|,
    |Omega4−4AUEV|<AUE|V|.

Therefore both have the sign of V, and

    |Omega2|<3AUE|V|,
    3AUE|V|<|Omega4|<5AUE|V|.                   (11)

For product2 with L=bV, (8),(11) and |b|>72g yield
2gy+|Omega2|<(15/2)g|V|<L/2.
For product4 with L=b², (7),(8),(11) give

    4gy+|Omega4|<(9/4)f|V|
      <(27/8)f²|b|<b²/4.                       (12)

The last inequality follows from |b|>7f³ and f>2. All bounds precede
sign recovery and cover negative b,V. We do not call Omega positive until
V itself has been proved positive.

## 5. Signed bootstrap, authentication, and projection order

The inverse correction satisfies e*=e6/6<=k−R−1<b for every integer R,
so rho<|b|/q⁷. In both weights L>0 and L>=|b|. If B<=−1,
Wt0=B/h+LB<−L. Solving(2) for positive n and using(9)–(12),
positive kappa,sigma, and q⁷>2 gives

    n< L/2−L+|b|/q⁷<0,

a contradiction. Thus B>=0, and (K0+w)C=B+F>0 gives C>0.
Only now use the selected whole tuple's rank bound3q<R<q⁴−2.
As c>4q⁴>2R, b,V are positive. The unchanged normalized main-index
and signed auxiliary-index theorems applied to V≡−c modf and V≡−R modc
identify p=R. Mask parity now gives q even,J odd.

Every Omega is an integer polynomial. Its numerator contribution M Omega
is divisible by D and H, so all subsequent modular reductions are exactly
those of parent/PROOF.md sections4–5. We state their noncircular order.
First k=2psi_(1+2v)(m) is even and e* is integral. Literal cancellation
of6 in the rational carrier gives q⁴|e*. The full Lucas identity is

    k=2m+8v Cm+32v²Zm, Cm=binom(m+1,3), Zm>=0,
    3[e*−(2m−R−1)]=4v²[24Zm−Am Sm],
    Am=Cm+4vZm, Sm=k²+k(2m)+(2m)²−4.

With v=q³ws² the latter gives q⁴|e*−(2m−R−1) at every prime,
including3. Since m<R and R<q⁴, m=(R+1)/2. One does not yet infer
q⁷|e*. Write R=2r0+1; r0>=48. The lambda-uniform ratio theorem at
lambda=q,Y>=1 gives Y>X^r0/3 and X^(r0+1)<H. The full-product
projector bound, retaining6h, gives X=2^R. Hence q is a power of2;
rank growth supplies q⁶|X and v is divisible by q⁸. Only now does the
cubic identity imply q⁷|e*. Thus rho and kappa are integral.

The remaining carrier relation yields q³|Y and h|B, since W≡1 modh.
Therefore t0 is a nonnegative integer. The retained fixed-minus parity,
lambda-uniform half-binomial rounding and fresh native reconstruction at
A_source=Y(X+1)+2 produce actual source words for the selected whole
calibration. This base is not confused with A=qY(X+1)+1. The native
interpretation yields a finite syntactic ZFC refutation, not merely a
conclusion from elementary scalar boxes.

## 6. Constructive strictly positive completeness

Conversely, the chosen whole native/refutation calibration supplies fresh
canonical data q=2^a, X=2^R, R≡3 mod4,3q+1<=R<q⁴,q³|Y,C>0
and t0=B/h>=0 integral. Parent section6 is uniform in these data and
constructs the free-chart inputs w=X/q,s=Y, positive eta,zeta,i,T,
with c=psi_A(R), k=2psi_(1+2v)((R+1)/2), g>0,V>0,y>0 and

    g>kappa+sigma+|rho|.

No old packed word or strong period is reused across calibrations.
Every center is positive when V>0 by section4. Set, at the selected
transport and root scale,

    n=rgy+Omega+(1+hL)t0+rho−kappa−sigma.        (13)

All terms are integers and the preceding strict bound makes n>0.
The literal numerator satisfies z=rgy, so(1) vanishes. This construction
also handles possibly negative rho. For bV one may equivalently take
n_new=n_parent+(r−1)gy+Omega. For b² we use(13), not a claim that
subtracting bVB from an arbitrary positive parent n preserves positivity.
All ten independent coordinates have their declared strict positive domain.

## 7. Entire low-padding2963 native calibration

The new native proof, decoder, language and every historical ordinary
interface it names are retained in native2963/, with267 exact source pins.
Its complete proof is research/low-padding-independent/PROOF.md.
The admissible selector bijection g(0)=0,g(j)=j+1 (1<=j<=941) removes
exactly old forbidden selector1. It preserves and reflects the full language,
including the complete436-character seed,430 actions, renamed initializer928
and calibrated final tile941; it is not an unproved canonical subfamily.

There are3297 coefficient slots,976 weighted positions and978 physical
positions. Physical dummy977 and marker1005 have zero coefficient but
remain Boolean positions. A separate kernel monomial copies Start0 to1005.
All916 padding tests use bit2 of fields1..916. The sole clause is1956;
marker parity, Boolean temporal count, alignment, carries and reset tests
are proved before the resulting native interpretation. Soundness needs no
controller premise. Completeness uses the same tuple's discharged Pclp:

    rho_native=2^47, L_native=2963, d=139261,
    fixed prime factors47,2963, orders23,2962,
    spacing68126, auxiliary prime1362521,
    H residues29,2938,492699.

The finite checker reconstructs the exact four unsigned big-endian integers,
not just their boxes; MF_source adds beta once. Every raw/compressed hash,
bit length, minimal encoding, marker monomial and physical support is checked.
The complete native section12 constructs fresh canonical outer data matching
section6 exactly. The free-chart endpoint in section5 constructs fresh original
source witnesses, so the native sections5–8 apply. This establishes both
interfaces rather than substituting a new tuple into an old calibration.

The historical radix67 specialization is separately supplied with the full
parent finite recipe and little-endian payloads,295388 raw bytes. The
new tuple is a different specialized polynomial and is not claimed identical
to either radix67 or any older4177/4027 specialization.

## 8. Exact algebra, degree, and complete highest forms

The checker independently expands the center over Z[A,Ybar,k,U,b,c],
using weights(4,2,1,5,4,2). It compares the division-free actual graph
against(10) and the t-quotient identity. Put Def=Omega²−r²GV². The
weighted degrees of Omega and Def are

    quotient_t:59,106; product2:59,102; product4:59,94.

For quotient_t the exact root defect is

    C2²−4G=U²[4E(Rt−Qt)+Qt²]−4E.

No positivity of Rt−Qt is required. The full three defect leaders are

    16A^10 U^6 Ybar^10 b² k^8−16A^11 U^6 Ybar^8 b² k^8,
    4A^10 U^6 Ybar^8 b² k^8,
    8A^8 U^6 Ybar^8 b² k^8−48A^6 U^6 Ybar^12 b² k^8.

The complete output identity is

    P=Q[Z0²−2M Z0 Omega+M²Def]+r²M²G−(Z0−M Omega)².

Independent degrees are deg(Q,M,G,V)=(72,12,46,36).
For bV, degZ0=54; for b², degZ0=22. The corresponding summand bounds
are(180,197,202,70,142),(180,197,198,70,142), and
(116,165,190,70,142). In each case the defect summand uniquely dominates.
Let q0=beta J,k0=eta+zeta. The complete collected top forms are

    [P_quotient_t]_202 = 36864 q0^80 w^22 s^55 i^10 k0^32
                              (q0−F)²(s−w),
    [P_product2]_198 = 9216 q0^78 w^22 s^54 i^10 k0^32(q0−F)²,
    [P_product4]_190 = 18432 q0^74 w^18 s^52 i^10 k0^32
                              (q0−F)²(w²−6s²).

They have198,99,198 terms respectively and are nonzero for each actual
positive beta. All terms, not a selected numerical ray, are independently
collected. Every gate is covered by an exact free-ring cut, all registers,
inputs and ports are live, and both alternative operators at every gate
are rejected:194,222,238 corruptions per tuple. Normal and optimized
Python run the same checks, propagate their mode to child replays, and
produce equal receipts. Relocated replay uses only this package.
