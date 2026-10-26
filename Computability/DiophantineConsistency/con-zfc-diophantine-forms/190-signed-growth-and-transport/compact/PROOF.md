# A degree-190 equation in ten positive integers

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
This section is an ordinary mathematical proof, with inherited theorems
identified explicitly. Its literal polynomial is `equation.json`.

## 1. Result and source boundary

The new polynomial has ten **strictly positive** integer variables, exact
total degree 190, and 119 live binary arithmetic operations: 74 products,
24 sums, and 21 differences. A square and multiplication by a fixed numeral
each count as one product. This is not a ten-unrestricted-integer claim.

The exact same four-number BFS943/radix67 tuple as source 172 is retained.
It includes beta=2^590069-1 and the complete K0, MC, MF payloads and finite
reconstruction recipe. The new reduction proves in ZFC, using source 172's
identified native/refutation calibration, that a positive zero exists if
and only if a finite syntactic ZFC refutation exists. Negation gives the
required consistency equivalence over the stated positive domain. No
consistency assumption or test determines any coefficient.

This result synthesizes two previously separate mechanisms: source 172's
free quotient Y=s and source 178's whole-product polynomial center. Their
direct composition does not attain degree 190: its bV transport creates a
degree-197 cross term. The new transport U E b^2 keeps that cross term at
degree 184. Unlike the bare b^2 transport, its proof tolerates main Pell
index 3 and the associated auxiliary index 3. No claim of a global minimum
or literature-wide novelty is made.

The immutable comparison snapshot is ProveIt commit
d123610bc98fef2006bff1c9466bc3f1221003e7. Immediate dependencies are:

* `172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/` as retained in incoming
  `ConZFC_Pell_Growth_210_2026-10-25.zip`, `compact11/source172/`;
  the exact degree-214 parent SHA-256 is
  6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449.
* `178-polynomial-centers/whole_product/`, for the formal quotient identity
  and coefficient-majorant method, here rechecked at the different free chart.

The exact repository source links are recorded in `SOURCE_LINKS.json`.
The complete selected ordinary proof texts are retained under
`source/upstream172/`. In particular its `inherited/strict/upstream_lucas/parent/proof_sources/`
directory contains `universal_pell.tex` (classification and signed index
folding), `uniform_ratio.md` (the free-chart projector), `scaled_native.md`
(Section 1's named source theorem), and `indexed_native.md` (Section 4's
whole-tuple/native/compiler/refutation composition). This preserves the
ordinary mathematical interface, not the entire historical formal import
closure. The machine calibration is inherited, not re-proved by the new
119-gate checker.

These ordinary reductions do not constitute a newly compiled end-to-end
Lean/Rocq proof or an emitted object-language ZFC derivation. The separate
finite checker proves exact algebraic identities and reconstructs the fixed
numerals; it does not infer the unbounded lemmas from sample values.

## 2. Complete ordinary polynomial

The independent coordinates are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

Use the complete fixed tuple beta,K0,MC,MF, never arbitrary numbers merely
satisfying its elementary inequalities. Define polynomial abbreviations

    h=beta J, q=h+1, C=q-F-alpha,
    X=qw, Y=s, Yp=qY, k=eta+zeta, c=kY+eta,
    A=Yp(X+1)+1, Delta=A^2-1, H=4A-5,
    v=X Yp^2, ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C-F,
    U=ic^2, a=Delta U^2 E, F0=1+a, G=E F0,
    f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    eclear=6(k-R-1-q^4Y)-ell(k^2-4),
    D=6q^7, M=hDH.

Every letter here is an expression abbreviation, not an additional variable.
For the center set

    e2=(kYp)^2,
    S=(kYp)[ell+k-(kYp)(Yp+1)],
    theta=U^2 b,
    Rc=theta(3E+e2)-(b-c),
    Sc=4E^2+3S^2+e2^2,
    Omega=U[2S Rc+A(4EV-theta Sc)].

The new transport and carrier are

    L=UE b^2,
    Z=hD[H(n-LB-Omega)+K]-H[DB+h eclear].

The single polynomial is

    P=Q(Z^2-16M^2GV^2)+(16M^2G-Z^2).                 (2.1)

These formulas contain no variable exponents, factorials, divisions,
recurrences, or unspecified predicates. The literal circuit shares 4E
between 4E^2 and 4EV; this saves one operation against a direct rendering.

For proof only let

    rho=[k-R-1-vk(k^2-4)/6]/q^7,
    sigma=Y/q^3, kappa=K/H, t=B/h, z=Z/M,
    W=1+hL.

At every positive tuple, before any integrality assertion,

    z=n+kappa+sigma-Wt-rho-Omega.                    (2.2)

## 3. The inherited root facts remain valid

Only the carrier and the fixed square root scale 4 have changed. For every
positive input q>=32, X>=q, Yp>=q, c>=3 and A>q^2>=1024. The unchanged
identities are

    f^2=1+4aF0,
    Q=Delta(f^2-1)=4Delta^2 U^2 G,
    gcd(E,F0)=1.

Both V and M are nonzero. At a zero, (2.1) gives

    (Q-1)Z^2=16M^2 G(QV^2-1).

For a prime dividing G, neither Q-1 nor QV^2-1 is divisible by that prime.
Taking valuations proves that G is a positive square. Coprimality then
gives E=tau^2, F0=f0^2 and G=g^2 with positive integral tau,f0,g.
The retained adjacent-coefficient descent, applied to the initially
rational y=|z|/(4g), gives y integral and

    QV^2-(Q-1)y^2=1, z=epsilon 4gy, epsilon in {-1,1}. (3.1)

The factor 16 has even valuation everywhere and changes none of this
argument. With I=2Ug the strong pair satisfies

    f^2-Delta I^2=1, Q=(Delta I)^2, c^2 divides I.

The retained signed all-index folding theorem, using V=-c modulo f,
therefore gives c=psi_A(p), p positive odd. As c>=3, p>=3 and

    c>=c3:=4A^2-1=4Delta+3, c>X, K>0.              (3.2)

None of these statements uses a sign for B,C,R,b, or V, or divisibility
of Y by q. This is exactly the source-172 free-chart root interface.

## 4. A transport bound that includes auxiliary index 3

If b=0 then V=-c, and (3.1) would give

    0<y^2-c^2=(c^2-1)/(Q-1)<1,

impossible for integers. Thus b is nonzero and V has the sign of b,
because f>2c. In particular |V|>1. The auxiliary odd-index classification
at parameter Delta I gives |V|>=4Q-3, allowing index 3. Using c3<=c and
2c<f,

    |b| >= (|V|-c)/f
         >= 4Delta f-(c+c3)/f
          > 4Delta f-1 > 3Delta f.                  (4.1)

Also directly from the auxiliary norm and V=fb-c,

    y < (3/2)|V|,  |V| < (3/2)f|b|.               (4.2)

The useful root bound is sharper and simpler than the old f/6 bound:

    (AUE)^2-G=E(U^2E-1)>0, hence g<AUE.            (4.3)

Section 5 proves, independently of the signs B,C,R,b,

    sign(Omega)=sign(V), |Omega|<5AUE|V|.           (4.4)

Combining (4.1)-(4.4) gives

    4gy+|Omega|
      < 11AUE|V|
      < (33/2)AUE f|b|
      < [11A/(2Delta)] UE b^2
      < L/4.                                      (4.5)

The last strict inequality is equivalent to 22A<Delta=A^2-1 and follows
from A>1024. This is the new transport lemma. Its formal degree is 27,
versus 40 for bV, yet it remains valid when p=3. Replacing it by b^2 would
lose the factor UE and would not establish the displayed bound.

## 5. Exact polynomial center and its signed majorant

Treat A temporarily as an indeterminate over Z[Yp,k,U,b,c]. One has

    E=e2 A^2+e1 A+e0,
    e1=k^2Yp(1-2Yp-2Yp^2),
    e0=1+k^2Yp(Yp+1)[Yp(Yp+1)-1].

Write F=EV and let Qj be the formal polynomial quotient of F by A^j.
Source 178's free-ring identity, checked again independently here, is

    Omega=U(4AF-2Q1-Q3/2).                         (5.1)

This belongs to the integer polynomial ring: F=(b-c)E+
2U^2 b(A^2-1)E^2, so every coefficient of Q3 is even. The division-free
formula in Section 2 is exactly (5.1), not a numeric quotient or floor.

For any polynomial in A let F#(A) denote evaluation after replacing each
coefficient by its absolute value. Put delta=(Yp+1)/A. Since X,Yp>=32,
delta<1/16. Also |e1|<2e2(Yp+1) and 0<e0<=e2(Yp+1)^2. Thus

    E#(A)<=e2(A+Yp+1)^2, E>=e2 A^2(1-2delta), E#(A)<2E.

This gives

    F#(A)<2E(|b|+c)+8(A^2+1)U^2E^2|b|.

At a zero b is nonzero. Since c+1<2U^2E and
|V|>(f-c)|b|>Delta U^2E|b|,

    F#(A)/|EV| < 4/Delta+8(A^2+1)/Delta
                =8+20/Delta <10.

Deleting low powers gives |Qj|<=F#(A)/A^j. Consequently

    |Omega-4AUEV|
      <10U|EV|(2/A+1/(2A^3))
      <AUE|V|,

because A>=16. Hence Omega has the sign of V and
3AUE|V|<|Omega|<5AUE|V|, proving (4.4). No positive sign of the encoded
computation was used to establish this center estimate.

## 6. Soundness and the exact arithmetic handoff

Since k>=2, the inverse correction obeys

    k-R-1-vk(k^2-4)/6 <= k-R-1 < b.

The last inequality is b-(k-R-1)=cT-k+1>0, valid for every integer R.
Therefore rho<|b|/q^7. If B<=-1, then Wt=B/h+LB<-L. From (2.2),
(3.1), K>0, sigma>0, and (4.5),

    n=epsilon 4gy+Omega-kappa-sigma+Wt+rho
      <L/4-L+|b|/q^7 <L/4-L+L/2<0,

contradicting n>0. Hence B>=0, and B=(K0+w)C-F implies C>0.
The authenticated mask bounds now give 3q<R<q^4-2. Together with (3.2)
this implies c>2R, hence b,V>0. The source-172 normalized strong-index
and auxiliary-index arguments, using exactly V=-c mod f and V=-R mod c,
identify the main index p with R.

The center Omega is an integer polynomial. Therefore z+Omega is integral,
and (2.2) has exactly the same fractional part as the source-172 carrier.
The replacement W=1+hL still satisfies W=1 modulo h. Reduction modulo H
is unchanged because the entire center is multiplied by H. For precision,
the remaining source-172 proof proceeds in this order:

1. E=tau^2 yields k=2psi_(1+2v)(m) with m<R. The full finite Lucas
   expansion and inverse cubic identity imply q^4 | (2m-R-1), including
   every possible prime-three factor. Since |2m-R-1|<R<q^4, m=(R+1)/2.
2. The carrier gives H|6hK. The lambda-uniform projector and its strict
   whole-product bound force X=2^R. Hence q is a power of two.
3. Only after this conclusion may the proof recover q^7 divisibility of
   the inverse correction and thus integral rho. Projection gives
   integral positive kappa. The carrier then gives q^3|Y and h|B.
4. The retained fixed-minus, half-binomial, native reconstruction, and
   whole-tuple calibration give a finite syntactic ZFC refutation.

Thus no divisibility is borrowed from a later stage and no factor of 3 is
prematurely inverted. These exact inherited steps are recorded in the
included `source/parent172_PROOF.md` and its named source boundary.

## 7. Positive completeness

Conversely, source 172 constructs from a finite syntactic refutation the
same canonical outer variables and positive Pell witnesses, including
q^3|Y, X=2^R, t=B/h>=0 integral, b,V>0, and integral rho,kappa,sigma.
Its bound, for every chosen strong period seed, is

    g>kappa+sigma+|rho|.

Our new Omega is positive on these canonical witnesses. Define the remaining
positive coordinate by

    n=4gy+Omega+(1+hL)t+rho-kappa-sigma.

All terms are integral. Since y>=1 and t>=0, the preceding bound gives
n>0. The carrier is then z=4gy, so (3.1) makes (2.1) zero. Every independent
variable lies in its actual strictly positive domain. This is a fresh
existence construction, not an unjustified positivity-preserving shear.

## 8. Exact total degree and finite certificates

Let Z0 denote Z with Omega omitted. Set Dnorm=Omega^2-16GV^2. The complete
free-ring decomposition is

    P=Q[Z0^2-2M Z0 Omega+M^2 Dnorm]+16M^2G-(Z0-M Omega)^2.

In Z[A,Yp,k,U,b,c] with weights (4,2,1,5,4,2), the exact center has 84
monomials and weight 59; Dnorm has 594 monomials and weight 94. Its complete
highest part is

    [Dnorm]_94=8A^6Yp^8k^8U^6b^2(A^2-6Yp^4).

This is checked by collecting every coefficient. The actual degrees satisfy

    deg(Q,M,G,V,Z0,Omega,L)=(72,12,46,36,41,59,27).

The five summands in the decomposition have bounds 154,184,190,70,142,
respectively. Thus the only possible degree-190 source is Q M^2 Dnorm.
Put q0=beta J and k0=eta+zeta. Its exact highest homogeneous part in the
ten independent inputs is

    [P]_190=9*2^11 q0^74 w^18 s^52 i^10 k0^32
                    (q0-F)^2(w^2-6s^2).

For example the coefficient of J^74 w^20 s^52 i^10 eta^32 F^2 equals
9*2^11 beta^74, which is nonzero for the authentic fixed beta. The total
degree is therefore exactly 190. Gate-degree propagation alone would miss
the cancellation; the emitted exact sparse identities supply the proof.

`verify.py` imports no circuit producer. It authenticates the immutable
parent, all unchanged parent rows, all 29 actual center gates, topology,
every live input and fixed port, the complete norm defect, the whole output
identity, the actual leading form, all four numeral payloads by independent
finite reconstruction, and nonzero modular partial derivatives proving that
all ten inputs genuinely occur. These finite checks neither decide consistency
nor replace the preceding unbounded proof.

## 9. Comparisons and the unrestricted-integer target

At the pinned snapshot the pertinent measured positive-domain points are
10/214/87 (source 172), 10/208/116 (source 178), and 10/206/90 (incoming
Affine Horizons), where the entries are variables/degree/operations.
The present 10/190/119 lowers degree in this family at a higher arithmetic
cost. These are comparisons of explicit construction metrics, not global
minimality statements.

If an unrestricted-integer polynomial is wanted directly from this positive
component, substitute

    x_j=1+a_j^2+b_j^2+c_j(c_j+1), j=1,...,10.

The classical three-square theorem makes this a surjection from Z^3 onto
the positive integers. Indeed for n>=0 the representation
4n+1=u^2+v^2+w^2 has exactly one odd coordinate; writing the other two as
2a,2b and the odd one as 2c+1 gives n=a^2+b^2+c(c+1).
Thus the substituted equation has 30 unrestricted variables and degree380.
This elementary corollary is not offered as a competitive unrestricted-arity
record; the repository has much smaller unrestricted equations. The principal
novel metric here is the positive-domain degree reduction.
