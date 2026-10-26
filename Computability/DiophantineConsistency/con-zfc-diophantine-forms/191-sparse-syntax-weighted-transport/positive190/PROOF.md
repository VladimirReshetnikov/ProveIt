# Weighted square transport in the free Pell chart

This component gives an ordinary integer polynomial in **ten strictly positive
integer variables**, of exact total degree **190**, with **120 live binary
operations** (75 multiplications, 24 additions, 21 subtractions). It is a new
combination of source172's free chart and source178's whole-product center.
The additional mathematical step is the transport weight `L=b^2 U E`.
Neither the source178 weight `b^2` nor its exclusion of auxiliary index three
can be transferred to the free chart without proof. The new weight makes that
exclusion unnecessary.

The coefficient tuple is the complete, unchanged, calibrated four-port tuple
of the supplied parent. The final polynomial has no variable exponent,
factorial, quotient, radical or unspecified predicate. The ordinary proof,
composed with the parent's explicitly identified native/refutation theorem,
establishes in ZFC:

    no positive integer zero of P  <=>  Con(ZFC).

This does not prove Con(ZFC) or absence of zeros, and is not a new end-to-end
proof-assistant certificate or a global simplicity minimum.

## 1. The complete polynomial

Let `J,F,alpha,i,T,w,s,n,eta,zeta` be independent strictly positive integers.
All other letters below are polynomial abbreviations. Retain the actual fixed
tuple `(beta,K0,MC,MF)` of the parent and define

    h=beta J, q=h+1, C=q-F-alpha, X=qw, Y=s, ybar=qY,
    k=eta+zeta, c=kY+eta,
    A=ybar(X+1)+1, Delta=A^2-1, H=4A-5,
    v=X ybar^2, ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C-F, U=ic^2, a=Delta U^2 E,
    F0=1+a, G=E F0, f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k^2-4), D=6q^7, M=hDH.

For the whole-product center define

    e2=(k ybar)^2,
    S=(k ybar)[ell+k-(k ybar)(ybar+1)],
    theta=U^2 b,
    Rc=theta(3E+e2)-(b-c),
    Sc=4E^2+3S^2+e2^2,
    Omega=U[2S Rc+A(4EV-theta Sc)].

Finally put

    L=b^2 U E,
    Z0=hD[H(n-LB)+K]-H[DB+h(e6-6q^4s)],
    Z=Z0-M Omega,
    P=Q(Z^2-16M^2 G V^2)+16M^2G-Z^2.

The requested ordinary polynomial equation is `P=0`. The literal graph in
`equation.json` specifies every binary operation and all ten quantifiers.
The reuse of `UE` costs no hidden witness or arithmetic operation.

For the proof only define the rational numbers

    t=B/h, kappa=K/H, sigma=Y/q^3,
    e*=e6/6, rho=e*/q^7, z=Z/M, W=1+hL.

Direct algebra, before any divisibility assertion, gives

    z=n+kappa+sigma-Wt-rho-Omega.                 (1)

## 2. The inherited conclusions that are independent of the carrier

The complete argument is in `inherited/FREE_CHART_PROOF.md`, Sections 2--5.
Only its final norm, and not the particular carrier expression, is used to
establish the following facts before the sign of B is known.

At all positive inputs, `q>=32`, `X>=q`, `ybar>=q`, `A>q^2`, `c>=3`,
`U>=c^2`, `E>1`, `a>c`, `f>2c`, `Q>c^2`, and `M>0`. At a zero the
identities

    Q=4Delta^2 U^2G, gcd(E,F0)=1,
    (Q-1)Z^2=16M^2G(QV^2-1)

and prime valuations show that `E=tau^2`, `F0=f0^2`, `G=g^2` for positive
integers tau,f0,g. The extra factor16 is a square and does not affect that
valuation argument. The retained adjacent-coefficient descent applies to
the initially rational `y=|z|/(4g)` and shows that y is integral. Hence

    z=epsilon 4gy,  epsilon in {-1,1},
    QV^2-(Q-1)y^2=1.                            (2)

The signed strong and auxiliary folding arguments then give

    c=psi_A(p), p positive odd, p>=3,
    c>=4Delta+3>4q^4, K>0,
    b nonzero, sign(V)=sign(b),
    y<(3/2)|V|, |V|<(3/2)f|b|,
    |b|>4Delta f-1.                             (3)

These assertions allow the auxiliary index-three case. They do not presume
`q|Y`, `B>=0`, `R>0` or `b>0`. Since b, Delta and f are integers, the final
strict bound in (3) gives the convenient exact consequence

    |b|>=4Delta f.                              (4)

Also

    G=E+Delta(UE)^2 <= A^2(UE)^2,

so `g<=AUE`.

## 3. A uniform bound for the whole-product center

The source178 center identity and proof remain valid with the letter Y there
replaced by the independent polynomial `ybar=qY` here. We give the entire
needed bound to make the changed hypotheses explicit.

Temporarily regard A as an indeterminate u over
`Z[ybar,k,U,b,c]`. The exact polynomial E(u) is

    E(u)=e2 u^2+e1 u+e0,
    e1=k^2 ybar(1-2ybar-2ybar^2),
    e0=1+k^2 ybar(ybar+1)[ybar(ybar+1)-1].

Set

    F(u)=E(u)[(1+2(u^2-1)U^2E(u))b-c].

Let Qj be the ordinary polynomial quotient of F(u) by u^j, evaluated at A.
This is polynomial division in a formal indeterminate, not an input-dependent
floor or rational operation in the delivered polynomial. Because

    F(u)=(b-c)E(u)+2U^2b(u^2-1)E(u)^2,

Q3 has even integer coefficients. The exact identity is

    Omega=U(4AEV-2Q1-Q3/2).                     (5)

The division-free formula in Section 1 proves that Omega is an integer
polynomial. An independent sparse collection checks all its 84 monomials.

Write P#(A) for absolute-coefficient evaluation of a polynomial P(u). The
ratio `delta=(ybar+1)/A<1/16`, since X>=32 and ybar>=32. Thus

    |e1|<2e2(ybar+1),
    0<e0<=e2(ybar+1)^2,
    E#(A)<=e2(A+ybar+1)^2,
    E>=e2 A^2(1-2delta),
    E#(A)<2E.

Consequently

    F#(A)<2E(|b|+c)+8(A^2+1)U^2E^2|b|.

At a zero b is nonzero, and `c+1<2U^2E` and

    |V|>Delta U^2E |b|.

The latter follows from `|V|>=f|b|-c >= (f-c)|b|` and `a>c`.
It follows that

    F#(A)/|EV| < 4/Delta+8(A^2+1)/Delta
                 =8+20/Delta <10.

Deleting low coefficients gives `|Qj|<=F#(A)/A^j`. Equation (5), and A>=16,
therefore imply

    |Omega-4AUEV|
       <10U|EV|(2/A+1/(2A^3)) < AU|EV|.

Hence Omega has the sign of V, and, before any sign bootstrap,

    3AUE|V|<|Omega|<5AUE|V|.                   (6)

## 4. Why the new transport weight works

The weight `L=b^2UE` is positive at every zero, regardless of the sign of b.
Combining (2)--(4), (6), and `g<=AUE` gives

    4gy+|Omega| <11AUE|V|
                <(33/2)AUE f|b|
                <=[33A/(8Delta)]L
                <L/3.                         (7)

The final inequality follows from `99A<8(A^2-1)` for every integer A>=16.
In fact the current chart has A>1024, so the margin is much larger than needed.
The argument expressly retains auxiliary index three.

The inverse-Lucas correction satisfies `e*<=k-R-1<b` for every integer R:
`k>=2` and `b-(k-R-1)=cT-k+1>0`. Hence `rho<|b|/q^7<L/2`.
If B<=-1, then `Wt=B/h+LB<-L`. Using positive kappa,sigma and (1) gives

    n=epsilon 4gy+Omega-kappa-sigma+Wt+rho
       <L/3-L+L/2<0,

contradicting n>0. Thus B>=0, and the equation `B=(K0+w)C-F` forces C>0.

Only now use the actual fixed tuple's mask bound `3q<R<q^4-2`.
Together with `c>4q^4`, it yields b,V>0. The retained normalized strong
index and signed auxiliary-index theorem identify p=R. They use exactly the
same residues `V=-c mod f`, `V=-R mod c` and `c^2|2Ug` as the parent.
No prior sign or q-divisibility of Y was silently assumed.

## 5. The exact arithmetic and logical handoff

Omega is an integer polynomial, and L is an integer polynomial satisfying
`W=1 mod h`. The source172 proof of authentication and projection therefore
applies to (1) without alteration. For clarity, its order is:

1. The first Pell norm gives `k=2psi_(1+2v)(m)`, m>=2, and monotonicity gives
   m<R. Integral z and the literal denominator give q^4|e*.
2. The retained full Lucas identity

       3(e*-(2m-R-1))=4v^2[24Z_m-A_mS_m]

   with v=q^3ws^2 gives q^4|(2m-R-1) at every prime divisor of q, including3.
   Since |2m-R-1|<R<q^4, m=(R+1)/2.
3. Reducing the numerator modulo H gives H|6hK, with no illicit cancellation
   of6h. The lambda=q uniform ratio theorem and complete-product strict bound
   give X=2^R and positive integral kappa.
4. Since q|X, q is a power of2. Rank growth gives q^6|X, hence q^8|v.
   The same cubic identity then gives q^7|e*, so rho is integral.
5. Equation (1), with integral Omega and W=1 mod h, yields q^3|Y and h|B.
   Thus t=B/h is nonnegative integral.

These are the parent's canonical native outer conditions, at the same complete
calibrated four-number tuple. Its fixed-minus parity, half-binomial rounding,
fresh native reconstruction, and identified syntactic refutation calibration
produce a finite ZFC refutation. This uses the whole tuple's calibration,
not merely its scalar inequalities.

## 6. Positive completeness

A finite syntactic ZFC refutation supplies the source172 canonical outer data
and the same positive eta,zeta,i,T. In particular b,V>0, t>=0 is integral,
and rho,kappa,sigma are integral. The retained canonical estimates give

    g>kappa+sigma+|rho|.

Keep those variables, and set

    n=4gy+Omega+(1+hL)t+rho-kappa-sigma.

Every term is an integer. By (6), Omega>0, and y>=1 and t>=0 make n strictly
positive. The carrier has z=4gy, so the norm equation vanishes. This completes
both directions of positive solvability versus syntactic refutability.

All arithmetic arguments and the retained proof-code equivalence are
formalizable internally in ZFC. Taking negations yields the stated consistency
equivalence, without assuming consistency or external standardness of proof
codes.

## 7. Exact degree and complete leading form

In the free chart the degrees are

    deg(A,ybar,k,U,b,c)=(4,2,1,5,4,2),
    deg(Q,M,G,V,E,Omega,L,Z0)=(72,12,46,36,14,59,27,41).

Independent sparse algebra in `Z[A,ybar,k,U,b,c]` gives, for
`Dnorm=Omega^2-16GV^2`, exactly 594 monomials, weighted degree94, and

    [Dnorm]_94
      =8A^6 ybar^8 k^8 U^6 b^2(A^2-6ybar^4).

The complete exact decomposition

    P=Q[Z0^2-2MZ0Omega+M^2Dnorm]+16M^2G-(Z0-MOmega)^2

has respective degree bounds154,184,190,70,142. Thus only the norm-defect
term can reach190. Put q0=beta J and k0=eta+zeta. Actual highest-component
substitution yields the entire degree190 form

    [P]_190 = 9*2^11 q0^74 w^18 s^52 i^10 k0^32
                    (q0-F)^2 (w^2-6s^2).        (8)

It is nonzero for the supplied positive beta. Therefore190 is the exact
degree of the actual fixed polynomial, not a generic-port estimate or a
naive propagation bound through its graph.

The comparison is 10 positive variables/90 operations/degree206 for the
incoming centered free chart, and 10/116/208 for source178's scaled whole
center. The new profile is 10/120/190: a measured degree improvement at a
higher operation cost. It is not a simultaneous improvement of every metric.

## 8. Further research

The weighted transport theorem permits other integer polynomial centers,
provided their signed magnitude has the same uniform O(AUE|V|) bound.
Reducing the 30-gate center evaluator while preserving its exact cancellation
is a concrete next target. Another is a lower weighted-degree polynomial
approximation to the full radical product; divisions by A or w cannot be
introduced into the final polynomial without paying for a new witness or
proving polynomial divisibility.

The current degree94 defect contains the term
`-48A^6 ybar^12 k^8 U^6 b^2`; merely adding the next Laurent term in the
source178 expansion removes the other top term but retains this one. Thus a
longer copy of that same A-Laurent truncation does not by itself lower the
degree190 endpoint. Finite checks verify algebraic identities and the literal
graph; they do not replace any unbounded Pell or logical proof.
