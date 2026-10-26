# A complete thirteen-positive-variable carrier at the2471 tuple

Author: ROOT. This ordinary proof transports the second-Pell carrier to
the complete accepted phase-split2471 native tuple, and then applies the
scaled-auxiliary identity to obtain degree140. Independent review and a
complete literal-graph audit are separate artifacts; this text does not
claim that its author's proof is independently reviewed.

The carrier idea and its69-operation schedule are credited to source192,
`con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/PROOF.md`,
SHA256 `5d210d457196c40bec061ecd79b86eeb1aeabb46a3d5e037d88bc34773fba07f`,
and its entire `positive13_square.json`, SHA256
`9574f3db6cfc549d565d278f84d7d9f0a53fec92cdcc05762c95d1e54db49c7c`.
ROOT read both complete files as inert text. No incoming program or TeX
was executed, and none of that source's older fixed ports is adopted.
The lower-degree identity was established separately in
`../scaled-auxiliary118/PROOF.md`; its thirteen-coordinate extension is
proved again below with the actual new strong factor.

## 1. Four exact ports and the complete polynomial

Use the four integers beta,K,MC,MF_source in the accepted
`../phase-split-independent/PROOF.md`, SHA256
`934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`.
Its complete finite certificate has SHA256
`f6c576194bfd60d10457c6ba9c43c0b7a8537639588c4f022e7a0362b9051bef`.
That theorem defines every coefficient and proves the complete native
and positive P66 equivalence. The fourteen-variable theorem subsequently
applied there is `../carrier65-independent/PROOF.md`, SHA256
`53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`.

The tuple is L=2471, d=116137, doubled clause1462 and marker1004.
Its complete unsigned ports total58125 bytes:

| Port | Bytes | SHA256 |
| --- | ---: | --- |
| beta |14518|`4a9d0f18ed31c9f1759c106b71244a8a04caf3c8cf128a7241fc280052825cc4`|
| K |14571|`9a863e00e5f9415c1a07d57959f632d0957eabd6967c58cd7822b1eaa116f449`|
| MC |14518|`c5c1f555895bad3c17c23d3a10e61bb72ff830124be74abca843c01477f88871`|
| MF_source |14518|`aed04479ff9beef8912ffb366b19d3259d672a680d150721c8a0fc2027b8b13e`|

In this proof write MF for MF_source, including exactly its one beta
shift. The native theorem proves

    beta>=31, K>0, 0<MC<beta<MF<2beta.                 (1)

The thirteen independent unknowns are strictly positive integers:

    J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma.

All following symbols are polynomial abbreviations:

    b=beta*J, q=b+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4*a+3,
    Delta=a^2+H, D=X+a*c+gamma*H,
    R=[b*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    tau=E*n+k-R, G=(K+w)*C-F,
    V=f^2*(c*T-R)-c, S=b*i*Delta*c^2,
    y=1+4*[b*(m-V^2*G)-G],
    P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2,
    Z=Delta*f^2-S^2,
    Uold=S^2*(V^2-y^2)+y^2,
    Theta=Delta*(f^2-1), U=Theta*(V^2-y^2)+y^2.

The lower-degree equation is

    p=P*Q*U*Z-Delta=0.                                (2)

For the carrier proof first use `pold=P*Q*Uold*Z-Delta`.
The signed value y and the transport expression G are not independent
unknowns. The final equation has integer coefficients and no variable
exponent, floor, quotient or unspecified predicate. Its fixed constants
are the complete accepted tuple above, not a mixture of specializations.

## 2. A signed auxiliary Pell pair and its full residue

For any integer S>=2 let chi_S(r),psi_S(r) be the integral Pell sequences
defined by the coefficients of `(S+sqrt(S^2-1))^r`. Their odd ordinate
subsequence satisfies

    u0=1, u1=4*S^2-1,
    u_(j+2)=(4*S^2-2)*u_(j+1)-u_j.

Induction modulo4*S^2 gives

    psi_S(2*j+1)=(-1)^j mod4*S^2.                    (3)

Suppose integer V,y obey

    S^2*V^2-(S^2-1)*y^2=1.                           (4)

Neither is zero. Every positive solution x,u of
`x^2-(S^2-1)*u^2=1` with u>1 descends by multiplication by
`S-sqrt(S^2-1)`. Its new ordinate `S*u-x` is strictly between0 and u,
because `sqrt(S^2-1)<x/u<S` and `sqrt(S^2-1)>S-1`.
The new abscissa `S*x-(S^2-1)*u` is positive because
`sqrt(S^2-1)>(S^2-1)/S`. The terminal positive pair is(S,1).
This proves the complete positive classification by reversing descent.

Apply it to x=S*abs(V), u=abs(y). The chi recurrence moduloS has
even-index values alternating1,-1 and odd-index values0, so divisibility
of x by S forces an odd index. Equation(3) then gives
`y=1 or -1 mod4*S^2`, including both signs of y. If y=1 mod4, only
the plus residue remains. Thus

    4*S^2 divides y-1.                               (5)

Also(4) implies `y^2 < S^2*V^2/(S^2-1) < 4*V^2`, hence

    abs(y)<2*abs(V).                                 (6)

These facts use no native rank, alignment, sign of G or positivity of V.

## 3. Soundness of the thirteen-variable carrier

For every positive assignment b>=31, c>1, Delta=(a+2)^2-1>1 and S>=2.
In particular

    Z=Delta*[f^2-Delta*(b*i*c^2)^2].

At a zero of pold, cancel the positive Delta. The four integer factors
P,Q,Uold and Z/Delta have product1 and hence each is a unit. The complete
consecutive-product obstruction proved in the accepted Carrier65 theorem
excludes P=-1: `ell*(ell+k)=E*Y*(E*Y+1)*k^2`, and E*Y>=2.
That argument does not assume a sign for tau. Since Delta is0 or3 modulo4,
neither Q nor Z/Delta can be-1. Since S^2 is0 or1 modulo4, Uold is
congruent to y^2 or V^2, and it also cannot be-1. Therefore

    P=Q=Uold=1, Z=Delta.                              (7)

No sign of C,R,G or tau was needed. The auxiliary equality is(4), and
the literal y is1 modulo4. Equation(5) and b|S imply

    b^2 divides b*(m-V^2*G)-G,

so b divides G. This is valid without b being odd, prime or squarefree.

Put L=V^2. Then L>=abs(V)>=1 by(4). If G<=-1, positivity of m gives

    y=1+4*[b*m-(1+b*L)*G]
      >=1+4*[b+1+b*L] >4*b*L >=4*abs(V),

contradicting(6). Thus G>=0, and `z=G/b+1` is a positive integer.
The deleted native factor is exactly restored:

    (K+w)*C+(q-F)-z*b=G+q-z*b=1.

Keep the other parent inputs, replace the parent's i by b*i, replace
its positive y by abs(y), and use this z. The parent's S is now exactly
our S; its auxiliary expression depends only on y^2. Every Carrier65
factor therefore has the value in(7) or the restored transport value1.
Its complete polynomial vanishes. The accepted whole Carrier65/native
soundness theorem supplies a finite syntactic ZFC refutation.

This is a map from every positive zero of pold. It does not assume
canonical data to prove soundness, and it recovers C and the rank bounds
only after the whole map to the accepted parent is established.

## 4. Fresh-seed completeness at the actual2471 ports

Conversely a finite syntactic refutation supplies the actual native data
of the accepted2471 theorem, sections9..12. Its complete P66 construction
and Carrier65 corollary give positive outer inputs with

    P=Q=1, C>0, F<q, X=2^R,
    R=3 mod4, c=psi_(a+2)(R), R>q*(q^2-1),
    b divides G, and n=(tau-k+R)/E>0.                 (8)

These outer data and the first-root carrier do not depend on the private
strong seed f,i or auxiliary coordinates T,y. The native theorem already
supplies every changed mask, controller, origin and rank obligation; no
old packed witness or constant tuple is substituted here.

The rank bound with q>=32 gives `2^R>q^2`, so `w=X/q>q`. Consequently

    G=(K+w)*C-F>w-q>0.                               (9)

Choose a positive Pell pair `f^2-Delta*I^2=1` with `b*c^2` dividing I.
To see existence directly, the unit `(a+2)+t` of norm1 in the finite
ring `(Z/(b*c^2)Z)[t]/(t^2-Delta)` has finite multiplicative order.
That power of the positive real Pell unit has I divisible by b*c^2,
with I>0; its positive powers give arbitrarily large such pairs.
Set `i=I/(b*c^2)>0`, making `S=Delta*I` and Z=Delta.

Write A=a+2 and R=2*j+1; j is odd by(8). The odd-index polynomials

    Q0(u)=1, Q1(u)=4*u-3,
    Q_(j+1)(u)=(4*u-2)*Q_j(u)-Q_(j-1)(u)

give `chi_S(R)=S*Q_j(S^2)`, `Q_j(0)=(-1)^j*R`, and
`Q_j(1-A^2)=(-1)^j*psi_A(R)`. The last identity follows from the same
recurrence: the signed odd psi subsequence has coefficients2-4*A^2
and initial values1,3-4*A^2.

Set `Vstar=chi_S(R)/S>0` and `ystar=psi_S(R)>0`. These are integers.
Since `S^2=Delta*(f^2-1)=1-A^2 modf^2` and c divides S, the identities
above imply

    Vstar=-c modf^2, Vstar=-R modc.

Moreover f^2=1 modc, so gcd(c,f)=1. Hence the witness

    T=(Vstar+c+R*f^2)/(c*f^2)

is a positive integer, and the literal V equals Vstar. These quotients
belong only to the witness construction, not to the polynomial evaluator.

By(3), ystar=-1 modulo4*S^2. Choose the signed target y=-ystar and set

    m=(y-1)/(4*b)+(1+b*Vstar^2)*G/b.                 (10)

This is an integer because4*b divides y-1 and b divides G. It is
strictly positive: G/b>=1 by(9), and(6) gives

    m>-(2*Vstar+1)/(4*b)+1+b*Vstar^2>0.

Equation(10) makes the actual polynomial abbreviation y equal its signed
target. All four factors in(7) have their prescribed values, so pold=0.
All thirteen independent inputs are positive. This is an existence map
using a fresh strong seed, not an identity of all parent/child zero sets.

## 5. The degree140 replacement preserves the whole positive zero set

At a zero of either p or pold, cancellation of Delta again forces the
integer Z/Delta to be a unit. Its residue modulo4 is a square or a sum
of two squares, and hence cannot be-1. Thus Z=Delta on either zero set.
The full polynomial-ring identity is

    p-pold=P*Q*Z*(Z-Delta)*(V^2-y^2),                 (11)

because `Theta-S^2=Z-Delta`. It follows that p and pold have identical
entire positive zero sets, by the identity map on all thirteen inputs.
No sign of y, V, G, C or R is needed for this identity argument. In
particular there is no need to assume a sign for the new factor U before
using(11). Sections3..4 therefore prove the full consistency equivalence
for(2), including every positive zero, with the exact current ports.

## 6. Integer circuit and exact total degree

The complete69-row source192 graph was read as data. Moving its existing
`scaled_f2=Delta*f^2` before the auxiliary product, adding the single
subtraction `Theta=scaled_f2-Delta`, and replacing that product's S^2 input
by Theta constructs70 integer-leaf operations. The other input V^2-y^2
and every other operation are retained; S^2 stays live in Z. The operation
counts are39 multiplications,16 additions and15 subtractions. A complete
new materialization and finite audit must separately check every row,
leaf, dependency, degree cancellation and whole fixed-port binding.

For the hand degree calculation put q0=beta*J, k0=eta+zeta and
C0=q0-F-alpha, all homogeneous of degree1. The leading forms are

    G0=w*C0,
    y0=-4*q0^7*k0^2*s^2*w*f^4*T^2*C0,
    Theta0=w^2*s^2*q0^8*f^2,
    U0=-16*q0^22*k0^4*s^6*w^4*f^10*T^4*C0^2,
    Z0=-i^2*w^4*s^8*k0^4*q0^30.

Thus y,Theta,U,Z have exact degrees19,14,52,48. The first norm P has
degree22, and Q has degree18 from the exact retained identity
`Q=(X+gamma*H)^2+2*a*c*(X+gamma*H)-H*c^2`.
Their leading forms are respectively `-w^2*s^4*q0^14*k0^2` and
`8*gamma*w^2*s^3*q0^11*k0`. Their complete product is nonzero:

    -128*q0^77*gamma*i^2*k0^11*w^12*s^21*f^10*T^4*C0^2.

The coefficient of `J^79*gamma*i^2*eta^11*w^12*s^21*f^10*T^4`
is `-128*beta^79`, which is nonzero for the actual fixed beta. Therefore
the exact total degree of(2) is140. This gains one positive unknown
against Carrier65 while adding five operations and lowering degree by10;
it is a tradeoff, not domination of every size measure.

## 7. Domain and retained logical boundary

The domain in(2) is explicitly the thirteen strictly positive integers.
If an unrestricted integer domain is wanted, replace each input by
`1+u^2+v^2+w*(w+1)`. This parametrizes every positive integer by the
three-square theorem applied to4*N+1: exactly one square is odd, and
subtracting1 and dividing by4 gives `N=u^2+v^2+w*(w+1)`.
Conversely each expression is positive for all integer u,v,w. This gives
39 unrestricted integers and, with the direct seven-operation substitution,
161 operations and exact degree280. No full lifted graph is claimed here.

Composing the complete maps with the accepted native/syntactic calibration,
ZFC proves that(2) has no positive integer zero iff Con(ZFC); the translated
equation has the corresponding unrestricted-integer equivalence. No
consistency assumption or decision is used. The proof is ordinary
mathematics with its retained foundational contracts, not a fresh
end-to-end Lean or encoded internal-ZFC replay. No global minimality or
actual unsolvability claim is made. The current fourteen-variable decimal
page remains unchanged until any alternative receives its own full graph,
source and visual review.
