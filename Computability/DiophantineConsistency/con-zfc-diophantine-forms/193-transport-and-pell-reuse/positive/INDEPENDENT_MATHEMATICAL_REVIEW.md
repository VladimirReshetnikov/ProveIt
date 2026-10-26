# Independent review of the ten-positive degree-190 construction

Review scope: ordinary mathematics and exact algebra of the new bridge. The
retained native/refutation calibration is inherited from source 172; this is
not a fresh end-to-end Lean/Rocq proof or an assertion of Con(ZFC).

## Sources actually inspected

* `172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/PROOF.md`, all sections.
* `178-polynomial-centers/whole_product/PROOF.md` and `ALGEBRA.md`, all sections.
* Incoming Affine Horizons, `positive/late172/PROOF.md`, all sections.
* Emitted `agent_baseline/new190/whole190.json` and its producer.

All paths are relative to the selected ProveIt snapshot
`cdfea7d90176775d74c1c30afbe49fa78ade9897` except the explicitly named
incoming extraction and new artifacts.

## 1. Definitions and the exact carrier

Use source 172's free-inverse chart, with independent positive integers
`J,F,alpha,i,T,w,s,n,eta,zeta`. Write `Y=s`, `y0=qY`,
`A=y0(X+1)+1`, `v=X*y0^2`, `E=1+k^2*v*(v+1)`, and keep all other
definitions of that source. In particular

    Delta=A^2-1, U=i*c^2, a=Delta*U^2*E,
    G=E*(1+a), f=1+2a, Q=4*Delta*a*(1+a),
    b=c*T-R, V=f*b-c, M=6*h*q^7*H.

Put

    e2=(k*y0)^2,
    S=(k*y0)*(ell+k-(k*y0)*(y0+1)),
    theta=U^2*b,
    Rc=theta*(3*E+e2)-(b-c),
    Sc=4*E^2+3*S^2+e2^2,
    Omega=U*(2*S*Rc+A*(4*E*V-theta*Sc)).

For a positive transport polynomial L, define

    Z=h*D*(H*(n-L*B-Omega)+K)-H*(D*B+h*eclear),
    P=Q*(Z^2-16*M^2*G*V^2)+16*M^2*G-Z^2.

The first tested choice was `L=U*E*b^2`. A cheaper literal evaluator uses
`L=A*U^3*b^2`. The latter does not require an explicit transport register:
replace Sc by `Sc-b*B` inside the Omega evaluator and use `n-Omega_modified`.
Indeed, identically over the integer polynomial ring,

    Omega_modified=Omega+A*U^3*b^2*B.

Thus the changed evaluator is exactly the same displayed P for that L.
This saves two gates: introduce `bB` and `Sc-bB`, then remove the four
old gates for `b^2`, `L`, `LB`, and the first subtraction from n. The old
final subtraction becomes `n-Omega_modified`. Counts are 118 versus 120,
subject to the producer's final independent liveness replay.

For proof only, put `t=B/h`, `kappa=K/H`, `sigma=Y/q^3`,
`rho=e*/q^7`, `W=1+hL`, and `z=Z/M`. Then exactly

    z=n+kappa+sigma-W*t-rho-Omega.

None of these rational proof abbreviations introduces a quantified witness.

## 2. Every pre-bootstrap bound is independent of B,R and the carrier

The final equation is

    (Q-1)*(z/4)^2=G*(Q*V^2-1).

The parent's prime-valuation and adjacent-Pell descent therefore apply to
the rational `z/4`. At every zero they give positive integers g,y with
`G=g^2`, `z=epsilon*4*g*y`, and

    Q*V^2-(Q-1)*y^2=1.

No sign or divisibility assumption about R,B or C enters this step. The
constant 16 is a square and cannot affect the valuation argument. The
parent's signed folding and auxiliary-index classification then give

    c >= 4*A^2-1, K>0,
    b != 0, sign(V)=sign(b), |V|>1,
    f>2c, y<(3/2)*|V|, |b|>4*Delta*f-1>3*Delta*f.

The auxiliary-index-three branch remains allowed. No argument excludes it
using a divisibility of Y that has not yet been established.

For the folded transport, the useful additional inequality is `E<U^2`.
Indeed `v=X*y0^2<A^2`, and `c>=4*A^2-1` imply `v+1<c`.
Also `k<c` because `c=kY+eta` and `Y,eta>=1`. All values are integral, so

    E=1+k^2*v*(v+1) <= 1+(c-1)^4 < c^4 <= U^2.

This proof is valid before B is known nonnegative and does not need a
lower bound on the first Pell index.

## 3. Signed whole-product center bound

As a polynomial in a formal variable A, holding y0,k,U,b,c fixed, write

    E=e2*A^2+e1*A+e0,
    e1=k^2*y0*(1-2*y0-2*y0^2),
    e0=1+k^2*y0*(y0+1)*(y0*(y0+1)-1).

Let F=E*V, and let Qj be the polynomial quotient of F by A^j. The
source-178 algebra gives the exact identity

    Omega=U*(4*A*F-2*Q1-Q3/2).

Here Q3 is coefficientwise even. This is proof notation for an ordinary
integer polynomial, not numerical division or a floor operation.

Since `delta=(y0+1)/A<1/16`,

    |e1|<2*e2*(y0+1), 0<e0<=e2*(y0+1)^2,
    E#<2E,

where # is absolute-coefficient evaluation at A. The literal identity
`F=(b-c)E+2U^2*b*(A^2-1)*E^2` yields

    F# < 2E(|b|+c)+8U^2|b|(A^2+1)E^2.

From `f>2c`, `|b|>=1`, and `c+1<2U^2E` one obtains

    |V|>Delta*U^2*E*|b|,
    F#/(E|V|)<8+20/Delta<10.

Deleting low coefficients gives `|Qj|<=F#/A^j`. Thus, for A>=16,

    |Omega-4*A*U*E*V|
      < 10*U*E*|V|*(2/A+1/(2*A^3))
      < A*U*E*|V|.

Consequently Omega has the sign of V and

    3*A*U*E*|V| < |Omega| < 5*A*U*E*|V|.

All estimates hold at negative b and negative V. In the free chart
`q>=32`, `X>=q`, `Y>=1` give `A>=1057`, so the mild numerical
requirements are safely satisfied.

## 4. The sign bootstrap is valid for either transport

The identity

    (AUE)^2-G=E*(U^2*E-1)>0

gives `g<AUE`. Using the bounds above,

    4*g*y+|Omega| < 11*A*U*E*|V|
                  < (33/2)*A*U*E*f*|b|.

For `L=UE*b^2`, the ratio of the last quantity to L is less than
`11*A/(2*Delta)<1/2`. For `L=A*U^3*b^2`, it is less than
`11*E/(2*Delta*U^2)<11/(2*Delta)<1/2`.

Also `rho<|b|/q^7<L/2`; its lower sign is irrelevant. If B<=-1,
then `(1+hL)*B/h<-L`, while kappa and sigma are positive. The exact
carrier identity would force

    n < 4*g*y+|Omega|-L+|b|/q^7 < 0,

contradicting n>0. Hence B>=0 and C>0.

Only after this step is the calibrated whole-tuple mask bound used to
deduce `3q<R<q^4-2`, and hence b,V>0. The remaining main-index
authentication, inverse-Lucas correction, H projection, recovery of the
power-of-two nature of q, full denominator divisibility, q^3|Y and h|B
follow in the source's stated order. Every altered transport and center
contribution is a multiple of M in Z, so all literal reductions modulo D
and H are unchanged. At the last step `W=1 mod h` still holds.

## 5. Completeness is constructive and independent of old n

The source's canonical data have t>=0 integral, b,V>0, and

    |rho|+kappa+sigma<g.

That inequality is explicitly proved in source 172 section 6 independently
of the transport L. Set

    n=4*g*y+Omega+(1+hL)*t+rho-kappa-sigma.

Every term is integral, Omega>0, and n>0. The carrier becomes z=4gy,
so P vanishes. This is a fresh witness construction; no unjustified claim
that an inverse shear preserves positivity is used.

## 6. Exact degree calculation

Use formal weights `(A,y0,k,U,b,c)=(4,2,1,5,4,2)`. Exact sparse
collection of the source-178 center identity gives

    deg(Omega)=59,
    deg(Omega^2-16*G*V^2)=94,

with full degree-94 component

    8*A^8*y0^8*k^8*U^6*b^2
      -48*A^6*y0^12*k^8*U^6*b^2.

In the actual inputs `deg Q=72`, `deg M=12`, `deg L=27`, `deg B=2`.
The uncentered carrier Z0 therefore has degree at most 41. Expanding only
the canceling square,

    P=Q*(Z0^2-2*M*Z0*Omega+M^2*(Omega^2-16*G*V^2))
       +16*M^2*G-(Z0-M*Omega)^2,

shows degree at most190; the cross term has degree at most184 and the
remaining correction at most142. Let q0=beta*J and k0=eta+zeta. The
entire degree-190 homogeneous component is

    9*2^11*q0^74*w^18*s^52*i^10*k0^32
      *(q0-F)^2*(w^2-6*s^2).

It is nonzero for the actual positive beta. Hence the degree is exactly190.
It contains198 terms before possible constant specialization; its two
different w/s exponent patterns prevent cancellation after specialization.

## Conclusion

The new bridge is mathematically sound at the named inherited calibration.
The weighted transport is the substantive new ingredient allowing the
whole-product center to work in the free chart without the old bV carrier
dominating the degree. Folding the alternative positive weight into Sc
reduces the implementation by two gates. No globally minimal polynomial,
worldwide novelty, or independent proof of consistency is established.
