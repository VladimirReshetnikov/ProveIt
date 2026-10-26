# Free-chart quotient centers with a signed, index-three-safe transport

## Result and attribution

There are two explicit ordinary polynomials in ten **strictly positive**
integer variables with exact (degree, live binary-operation) pairs
**(202,99)** and **(190,120)**. All four fixed ports are the WHOLE authenticated
Start-only4127 tuple (beta,K0,MC,MF), totaling97,046 raw bytes. The190/120
point is a degree improvement, not an operation improvement, over both the
frozen214/87 front and the incoming206/90 centered front. These statements
are not about ten unrestricted integers and do not change signed11.

The free Y=s, lambda=q chart, inverse Lucas correction, trace construction,
and native interface are inherited verbatim from `inherited_positive10/`.
The quotient centers and their exact polynomial-part interpretation are
credited to consolidated source178, frozen in `source_centers/`. The new
contribution is their free-chart composition and, for190/120, the transport
L=(UE)b²: unlike bare b², it is valid before rank recovery even when both
main and auxiliary index3 remain possible. No new global optimum,
consistency proof, independent foundational calibration or end-to-end
proof-assistant/object-ZFC certificate is claimed.

## 1. Complete equations

The independent inputs are J,F,alpha,i,T,w,s,n,eta,zeta>0. Put

    h=beta J, q=h+1, C=q-F-alpha, X=qw, Y=s, N=qY,
    k=eta+zeta, c=kY+eta,
    A=N(X+1)+1, Delta=A²-1, H=4A-5,
    v=X N², ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    B=(K0+w)C-F, U=ic², a=Delta U²E,
    F0=1+a, G=E F0, f=a+F0, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k²-4), D=6q⁷, M=hDH,
    S=(kN)[ell+k-(kN)(N+1)].

For202/99 choose

    r=2, L=bV, Omega=[2AUE-US]V.

For190/120 choose

    r=4, L=(UE)b², e2=(kN)², theta=U²b,
    Rc=theta(3E+e2)-(b-c), Sc=4E²+3S²+e2²,
    Omega=U[2S Rc+A(4EV-theta Sc)].

Finally define

    Z0=hD[H(n-LB)+K]-H[DB+h(e6-6q⁴s)],
    Z=Z0-M Omega,
    P=Q[Z²-r² M² G V²]+[r² M² G-Z²].

The equation is P=0. All capitalized and other named quantities above are
polynomial abbreviations, not quantified unknowns. All exponents are fixed
small natural numbers; the actual JSON uses only binary +,-,* with integer
leaves. All four port files are bound together in both emitted graphs.

For proof notation only, set t=B/h, kappa=K/H, rho=(e6/6)/q⁷,
sigma=Y/q³, z=Z/M and W=1+hL. Their exact rational identity is

    z=n+kappa+sigma-Wt-rho-Omega.                 (1)

No integrality of these quotients is presumed initially.

## 2. Root extraction and uniform pre-rank facts

The inherited_positive10/PROOF.md §2 root extraction applies unchanged:
its only carrier input is the rational z. The square r² changes no prime
valuation parity. It gives positive integers tau,f0,g,y and epsilon=±1 with

    E=tau², F0=f0², G=g², z=epsilon*r*g*y,
    QV²-(Q-1)y²=1,
    f²-Delta I²=1, I=2Ug, c²|I,
    c=psi_A(p), p positive odd.

The retained rational adjacent-Pell descent is applied to z/r: it proves
y=|z|/(rg) integral, not by assuming z or y integral at the outset. We have q>=32,N>=q,A>q², c>=3, p>=3 and
c>=c3=4Delta+3>4q⁴, hence c>X and K>0. These facts require neither C>0
nor any sign of R, b, V or transport quotient.

The full signed argument in inherited §2 proves b!=0, b and V have the
same sign, f>2c, f>6g, y<3|V|/2 and

    |b|>4Delta f-1>3Delta f,
    |V|<=f|b|+c<(3/2)f|b|.                      (2)

The last strict inequality uses |b|>=1 and c<f/2. In particular the
auxiliary index3 branch is allowed; it is not incorrectly ruled out.
Also

    (AUE)²-G=U²E²-E>0,
    (AUE)²/G < A²/Delta <9/4,

so g<AUE<3g/2. U,E are strictly positive directly from their polynomial
definitions on all positive inputs, independently of rank or any root.

## 3. Centers before signs: scalar and whole-product bounds

Regarding A as a formal variable over Z[N,k,U,b,c], write

    E=e2 A²+e1 A+e0,
    e2=k²N²,
    e1=k²N(1-2N-2N²),
    e0=1+k²N(N+1)[N(N+1)-1].

This identity is literal because v=N(A-N-1). Polynomial division gives
E=A S+e0 with exactly the S in §1. Since X>=32,N>=32,
S=k²N[(X-1)N²-N+1]>0 and e0>0, hence 0<S<E/A. Consequently the
202/99 scalar center C2=2AUE-US satisfies 0<C2<2AUE<3g, and

    2gy+|Omega|<6g|V|<L/2.                      (3)

Indeed (2) and f>6g give |b|>18Delta g>12g; here L=|b||V|.
For canonical positive V, Omega is positive.

For190/120 let F(A)=E(A)V(A), with
V(A)=[1+2(A²-1)U²E(A)]b-c. Let Qj be its formal polynomial quotient by
A^j. Its Q3 is coefficientwise even, since the degree<=2 part (b-c)E
does not contribute and the remaining part has factor2U²b. The exact
integer-polynomial identity is

    Omega=U[4AEV-2Q1-Q3/2].                     (4)

The division-free evaluator is precisely §1, as shown by the exact
quotient identities in source_centers/ALGEBRA.md with Y there replaced
by N here. Division and halves occur only in proof notation; Q3/2 is an
integer polynomial and the delivered evaluator has no division gate.

For completeness we retain the entire unbounded signed majorant argument.
For a polynomial in A let # denote absolute-coefficient evaluation at the
positive A. With delta=(N+1)/A<1/16,

    |e1|<2e2(N+1), 0<e0<=e2(N+1)²,
    E#<=e2(A+N+1)², E>=e2 A²(1-2delta), E#<2E.

Therefore

    F#<2E(|b|+c)+8(A²+1)U²E²|b|.

Use |b|>=1, c+1<2U²E, and
|V|>(f-c)|b|>Delta U²E|b|. The latter follows from a=Delta U²E>c
and f=1+2a. Thus

    F#/|EV| <4/Delta+8(A²+1)/Delta=8+20/Delta<10.

Deleting low coefficients gives |Qj|<=F#/A^j. Equation (4) now implies

    |Omega-4AUEV|<10U|EV|(2/A+1/(2A³))<AU|EV|.

Thus Omega has the sign of V and |Omega|<5AUE|V|<7.5g|V|. In particular

    4gy+|Omega|<13.5g|V|<16g|V|.                (5)

Here is the new transport estimate, valid for BOTH signs of b,V and for
the retained index3 branch. With L=UE b²>0, (2) and g<AUE give

    g|V|/L < (3/2)A f/|b|
             < A/(2Delta) <1/A.

The final inequality is A²>2. Since A>q²>=1024, (5) yields

    4gy+|Omega|<16L/A<L/2.                      (6)

No statement gy<b²/2 is used or claimed. The extra UE is essential to
this particular pre-rank bound.

## 4. Signed transport, first index, projection and native soundness

For either center, the inverse correction is nonnegative because k>=2,
so e6/6<=k-R-1<b for every integer R. Hence rho<|b|/q⁷. In both
cases L>=|b| (for190 use UE>=1 and b²>=|b|), so rho<L/2. If B<=-1,
then Wt=B/h+LB<-L. Solving (1) for n, using kappa,sigma>0, (3) or (6),
and the strict rho bound, gives n<L/2-L+L/2=0, a contradiction.
Thus B>=0, whence C>0. Only NOW the authenticated whole-tuple scalar
bounds give 3q<R<q⁴-2. Since c>2R, b,V>0; the unchanged strong-rank
and signed auxiliary-index theorems recover p=R, R odd, q even and J odd.

The carrier change is an INTEGER polynomial multiple of M, and L is an
integer polynomial. Hence all denominator reductions in the inherited
§§4–5 remain exact. In order, they prove:

1. E=tau² gives k=2psi_(1+2v)(m), 2<=m<R. The literal factor6 is canceled
   over the integers, not inverted modulo q. From integral Z0/M and
   gcd(q,hH)=1 one obtains q⁴|(e6/6).
2. The exact all-index cubic-difference identity, with v=q³ws², proves
   q⁴|(e6/6-(2m-R-1)) at every prime, including3. The bound |2m-R-1|<R<q⁴
   gives m=(R+1)/2. Neither q⁷ divisibility nor q³|Y is assumed yet.
3. H|6hK. The lambda=q ratio bound and full-product projection inequality
   give X=2^R without canceling6h through H. Thus q is a power of2, and
   rank growth gives q⁶|X, then q⁸|v and q⁷|(e6/6). Hence rho and kappa
   are integers.
4. Since Omega,z,n,kappa,rho are integers, (1) gives sigma-WB/h integral.
   Reduction modulo q³ gives q³|Y. Reduction modulo h gives h|B because
   W=1 mod h for EITHER L. Thus t is a nonnegative integer.

These are the SAME whole Start4127 native outer conditions:
X=2^R, q³|Y, C>0, and (K0+w)C-F=ht with t>=0. The complete fresh-source
reconstruction and whole-interface proof are retained locally in
inherited_positive10/PROOF.md §9, MATHEMATICAL_REVIEW_NATIVE.md and
native4127/START_ONLY_PROOF.md. They construct fresh unscaled Pell
witnesses at Y(X+1)+2 and decode an actual marked blank computation and
finite syntactic ZFC refutation. They do not infer a native theorem from
scalar boxes or mix separate coefficient ports. In particular MF is the
once-shifted Start4127 source mask, not shifted again.

## 5. Strictly positive constructive completeness

Conversely the SAME whole native Start4127 theorem supplies canonical
outer data from a finite refutation. Apply inherited_positive10/PROOF.md
§6 to construct all coordinates except n: positive strip coordinates,
a sufficiently divisible strong Pell period, and the positive auxiliary
trace-linear quotient T. Then b,V>0 and all the recovered rational
quantities t,rho,kappa,sigma are integers, t>=0. The inherited estimates
are |rho|<g/3 and kappa+sigma<g/2, including possibly negative rho.
Sections3 establishes Omega>0 for both centers. Choose

    n=rgy+Omega+(1+hL)t+rho-kappa-sigma.

This is a strictly positive integer, since r>=1,y>=1 and
g>kappa+sigma+|rho|. It gives z=rgy and hence P=0. No inverse shear of
an arbitrary positive tuple is asserted, and no new source/controller
assumption is used. Ordinary ZFC therefore proves, for either literal
specialization, positive solvability iff finite syntactic ZFC refutability;
negation is equivalent to syntactic Con(ZFC), without deciding either side.

## 6. Exact algebraic degree and operations

Use the weighted independent polynomial variables (A,N,k,U,b,c) with
weights (4,2,1,5,4,2). The exact base degrees are
(Q,M,G,V,UE)=(72,12,46,36,19). For202/99, deg Z0=54 and deg C2=23;

    C2²-4G=4U²E e0+U²S²-4E

has exact weighted degree34, with leading form4U²A²N^6k^4.
The dominant output degree is72+24+72+34=202; the cross term has degree197.

For190/120, deg L=27 and deg Z0=41. Exact collection of ALL594 monomials
of the defect Dwhole=Omega²-16GV² gives weighted degree94 and entire leader

    [Dwhole]_94=8A^6 N^8 k^8 U^6 b²(A²-6N^4).

The center has84 monomials and degree59. The exact output decomposition is

    P=Q[Z0²-2MZ0 Omega+M²Dwhole]
      +16M²G-(Z0-M Omega)².

Its summand upper degrees are154,184,190,70,142, respectively. Thus only
QM²Dwhole can contribute degree190, not a naive214 propagated bound.

Put q0=beta J and k0=eta+zeta. The actual complete highest forms are

    [P202]_202=9*2^12 q0^80 w^22 s^56 i^10 k0^32(q0-F)²,
    [P190]_190=9*2^11 q0^74 w^18 s^52 i^10 k0^32(q0-F)²(w²-6s²).

They contain99 and198 collected monomials. They are nonzero at the ACTUAL
positive beta: for example the F² eta^32 w^20 term in P190 has nonzero
coefficient9*2^11 beta^74. This proves the exact degrees, not just free-port
or generic-weight upper bounds. Dependence of A,N,U,b,c on the ten original
variables is included in this complete leading substitution.

Every actual gate, square, fixed-numeral multiplication and quantified
coordinate is counted. There are99 live operations for202 (60*,21+,18-),
and120 for190 (75*,24+,21-). The selected entire tuple is identical to the
frozen Start4127 tuple; its size and native semantic proof remain unchanged.
Finite algebra, mutation and numeral checks authenticate the artifacts, but
do not by themselves prove any unbounded Pell/native/refutation theorem.
