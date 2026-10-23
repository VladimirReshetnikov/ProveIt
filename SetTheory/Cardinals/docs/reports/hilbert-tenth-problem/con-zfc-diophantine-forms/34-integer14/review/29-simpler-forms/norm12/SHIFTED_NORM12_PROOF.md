# A stronger separation weight after shifting the index quotient

This note strengthens `COMPACT_NORM12_PROOF.md`. It retains all twelve
strictly positive coordinates and the same whole coefficient binding,
finite norm definition, root recovery and product parity argument. The
only mathematical changes are

    h_old=q+h,
    Nk=k-(q+h)E-R,
    W=I(T+I), L=1+HW.

Here h denotes the new supplied positive coordinate. All other symbols
retain their definitions in the compact proof. In the main product the
transport coordinate is unshifted. The110-operation system additionally
uses z_old=z+1, exactly as in the compact proof.

## 1. The revised weak bootstrap is noncircular

The substituted h_old=q+h is positive immediately because q,h>0.
At a product zero, the unchanged parity argument first gives N=0 and
Nk=Nt=epsilon in {+1,-1}. For the system, both outer equations are +1.
The inherited weak transport bootstrap yields Cw>=0, q>=16,
R>3q, R<q^4-2, X>=16, Y>=q^3 and E>=q^4>R+2.
No eliminated square root is used in these assertions.

Because h>=1, h_old>=q+1. Also

    q^4/E<=1, q^4/Y<=q,

and therefore

    (q+1)EY >= q^4(E+Y) > R a.

The outer index equation gives

    c=kY+eta=h_old E Y+(R+epsilon)Y+eta
      > R a+(R-1)Y > R(a+5).

The final strict inequality follows from R>=2 and Y>=4096, which imply
(R-1)Y>5R. In particular c>a and R<c. All old weak bounds continue
to hold. This reasoning concerns only integer polynomial values before
root recovery, so it is not circular.

## 2. The smaller weight bounds every auxiliary conjugate

The compact proof already establishes, using only I>=c^2, c>=2 and
Delta>=2,

    sqrt(Q/d)*c*sqrt(D) < I*sqrt(G),
    sqrt(Q/d)*a*c < sqrt(G),
    |y'| < sqrt(Q/d)*(c*T*sqrt(D)+b).

We improve the b estimate. As a>=5, Delta=a^2+4a+3<a(a+5).
The new inequality c>R(a+5) therefore gives

    R*Delta<R*a*(a+5)<a*c.

All quantities are integers, so ac-RDelta>=1. As c+R<I^2,

    b=c+R+RDelta I^2<ac I^2.

Consequently sqrt(Q/d)b<I^2 sqrt(G), and for every real or complex
auxiliary conjugate,

    |y'|<(TI+I^2)sqrt(G)=I(T+I)sqrt(G).

All separation, rationality, integrality, main congruence, signed-interface
and parity steps in the compact proof now apply verbatim. This proves
soundness without assuming the extra completeness bound in advance.

## 3. The coordinate restriction loses no compiler witnesses

The inherited fixed-blank proof, `21-norm12/upstream/FIXED_BLANK_67_PROOF.md`,
Section4, classifies the first Pell norm as

    tau=chi_P(n), k=2 psi_P(n), P=2EY+1,

and its final step proves 2n=R+epsilon and epsilon=1. Section2's rank
bound gives R>3q, hence n=(R+1)/2>=3. These are conclusions of the
complete old compiler theorem, used here only for completeness.

For the ordinary Pell sequence psi_P(3)=4P^2-1. Monotonicity therefore
gives

    k>=2 psi_P(3)=8P^2-2>32E^2Y^2.

Since R+1<E and R<E,

    k-R-1>32E^2Y^2-E>RE.

The old index equation yields

    h_old=(k-R-1)/E>R.

Since R>3q>q, h=h_old-q is a strictly positive integer. Every old positive
compiler solution admits this coordinate shift, so in particular every
canonical accepting solution does. With the new W set
r=gamma+W*u+L*tau+y exactly as before. The construction gives all new
positive coordinates, N=0 and Nk=Nt=1.

This establishes the required existential equivalence. Composing with
the unchanged coefficient/compiler theorem and K215 logical endpoint
gives, within ZFC, absence of positive solutions iff Con(ZFC).

## 4. Exact arithmetic size and leading degree

The change h_old=q+h costs one addition. The weight W=I(T+I) uses only
two gates, one fewer than I(T+kI). Thus all operation counts remain
the same as the compact family:

| Construction | Variables | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Shifted system | 12 positive | 3 | max1088 | 110 |
| Unshifted-transport system | 12 positive | 3 | max1088 | 111 |
| Product | 12 positive | 1 | 1097 | 116 |
| Shifted sum of squares | 12 positive | 1 | 2176 | 118 |

Here shifted system means both h_old=q+h and z_old=z+1; the product
uses only the h shift. All gates and input ports are live.

The new weight degree is22, L degree28 and a0=H^2L^2A degree90.
The scalar C0=d(V0+a0)-H^2 e has unique highest term d*a0, degree136;
H^2 e has degree134 and dV0 degree124. The odd coefficient C1 has
degree85. Subsequent pair arithmetic gives deg(N0)=544 and
deg(N1)<=493, so deg(G N1^2)<=1008. Thus deg(N)=1088 with no
top-degree cancellation. In terms of q0=beta J and k0=eta+zeta,

    N_top=2^64 i^48 k0^112 w^80 s^192 q0^656.

The revised index factor has degree7 and leading term

    (Nk)_top=-(q0+h)(E_top)
            =-(q0+h)w s q0^4.

The unchanged transport factor has degree2. Hence product degree is
1088+7+2=1097. For example, the coefficient of

    J^661 h z i^48 eta^112 w^81 s^193

is +2^64 beta^661, so the degree is uniform for every beta>0.
The norm squared is the unique highest-degree SOS summand, giving2176.

`build_shifted_norm12.py` emits the complete comparison systems and
polynomials. Its48 independent conjugate-product checks,48 transport
shift/SOS checks, mod64 guards, all-input/gate liveness checks and three
modular leading-form checks pass. The mathematical proof, rather than
these finite checks, establishes semantic equivalence and uniform degree.
No new Lean/Rocq proof and no unrestricted-integer extension are claimed.
