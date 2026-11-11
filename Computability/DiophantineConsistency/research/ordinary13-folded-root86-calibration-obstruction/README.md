# Calibration-route dependency and a compact44 partial obstruction

This source-traced analysis is submitted for independent review. The existing
free-J calibration route uses positivity of the **old** first-root input to
obtain `Bt>0` and `C>0`; a positive sign-reversed 86 input does not supply
that hypothesis. A concrete symbolic partial assignment below at the
**authenticated compact44 ports** has all inputs positive, `Bt<0`, exact
first residual zero, a valid first Pell root with k>2, and a valid *bare*
main Pell unit. It is **not a full zero**: its actual main residual cannot
vanish for any positive gamma. This documents the gap in the existing route,
not a mathematical impossibility of another route or of reverse existence.
No Lean theorem, halt claim, PDF/file semantics or global nonequivalence is
claimed.

## Exact dependency in the existing source

`FreeJFirstTransport.freej_first_factor_transport` assumes `hv : ∀j,0<v j`
for the old 12-coordinate literal. In the proof, `v 7` occurs positively in
`M*(ell+k+v 7)`; the contradiction against `t<ell+k` establishes `Bn<Bp`.
Its definitions give `Bp−Bn=Bt`, and then the proof derives
`q>F+alpha`, equivalently C>0. Under the signed fold the old coordinate would
be `v 7=k*Bt−sigma`, which is not positive when Bt<=0. The first proof step
therefore cannot be invoked with its hypotheses satisfied in that branch.

`CompactLeafFactsLiteral.of_literal` calls that theorem directly for its
`transport` field; `FreeJSaturationClient.graph_saturation`,
`FreeJPowerProjection.graph_projection`, and `FreeJPowerFinish.graph_power`
also use its gap. The separately stated `P72Window.window_ring` explicitly
assumes a positive C in `q=F+C+alpha` to prove its rank window. These are
source-level dependency observations, not a complete transitive provider
trace and not a proof that another calibration argument cannot work.

## Actual-port first-root and bare-main-unit control

Let `(beta,K0,MC,MF)` be the four P72 compact44 payloads authenticated
against P115: `beta=2^590069−1`, K0>0, MC>0, MF>0. Put

```
b=beta, q=b+1, J=1, F=1, alpha=q, C=−1,
s = the representative in {1,...,b} of (1−K0)*2^(-1) modulo b,
Y=q³*s, X=2Y−2, m=X*Y², P=2m+1,
k=4P, tau=2P²−1, ell=m*k,
a=XY+Y=2Y²−Y, A=a+2, H=4a+3,
c=4A²−1, eta=c−Y*k=36Y²−20Y+15,
zeta=k−eta=16Y³−52Y²+20Y−11,
Bt=−(X+K0*q)−q, t=Bt/b,
sigma=ell+k+s−t−tau=4m+3+s−t.
```

The inverse of 2 exists because b is odd. Since `q≡1 (mod b)` and
`X≡2s−2 (mod b)`, the definition of s makes `b|Bt`. All displayed natural
inputs J,F,alpha,X,Y,eta,zeta,sigma are positive: q and Y are enormous,
`eta>0` and `zeta>0` already for Y>=4, and `t<0`. The remaining f,i,T,u and
gamma may be any positive integers for this partial assignment.

The first norm holds exactly, `tau²=1+m(m+1)k²`; with M=q³b,

```
Z=M*(ell+k−sigma)+Y*b−q³*Bt = M*tau,
```

so `A0=0` while `Bt<0` and k>2. Moreover `c=Y*k+eta` and the bare main Pell
unit is exact:

```
d=4A³−3A > 0,   d²=1+(A²−1)c².
```

Here the rank uses `G=b(q−F)+alpha=b²+b+1`, so
`R=G(q²−1)+MC+q*MF>0`.

## Why this is not a full zero

Suppose the actual main residual A1 vanished for any positive gamma. Its
`Dstar=U*(X+a*c)+H*(U*gamma+X*Y*q−k+R+1)`, with U=Yq², would be positive:
`c>Yk`, `H<=7a`, `Y²q²>7` and `R>0` imply
`Dstar>U*a*c−H*k>0`. From A1=0, U|Dstar and the positive main root is exactly
d. The identity

```
d−a*c = 8+H*(2a+6)
```

therefore forces `H | U*(8−X)`. But H is odd, `gcd(H,q)=1` because
`H≡3 (mod q)` and q is a power of 2, and `gcd(H,Y)|3`; hence
gcd(H,U)<=3. Since `X−8=2(Y−5)` and `H mod (Y−5)=183`, this divisibility
would imply `H/gcd(H,U)|183` and therefore `H<=549`. Actual Y>=q³>9 gives
`H=8Y²−4Y+3>549`, contradiction. The candidate is consequently not a full
zero, regardless of the auxiliary coordinates. This also identifies the
main projection/divisibility obligation that this simple negative-Bt
construction fails.

The checker authenticates all port bytes against both bindings, pins the
listed source files, verifies the actual modular scalar choice and evaluates
small exact polynomial controls. It does not expand the enormous symbolic
witness or replace the unbounded arguments. No Lean build is performed.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-calibration-obstruction-independent/`.
