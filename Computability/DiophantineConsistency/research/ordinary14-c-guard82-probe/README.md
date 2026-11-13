# A provisional actual-port zero after dropping the transport guard

This packet proposes a **full symbolic positive zero** of an 82-operation,
14-positive-input probe obtained by replacing the reviewed 87/26 shifted
transport guard with the weaker guard `C−omega=0`. It uses the authenticated
compact44 ports beta, MC and MF; K0 is no longer a graph leaf, but is used
below to test the omitted transport congruence. The construction is
submitted for independent review. The enormous Pell inputs are specified
exactly but not expanded. The result does not settle unrestricted
positive-zero equivalence with the parent at other q and R, prove a zero of
the 14-variable PDF equation, or give a Lean/iPRA theorem.

The probe is not proposed as a consistency equation. The first norm, main
norm, strong norm and auxiliary norm are retained from the quotient-guarded
88/26 graph; its new fifth squared residual is `(C−omega)²`. From the
87/26 probe this deletes five transport-computation gates. There are 82 live
operations, 14 distinct positive inputs, three live fixed leaves, and exact
specialized degree 26, subject to the same external degree argument.

## Exact actual-port seed

Authenticate the P72 and P115 compressed and raw little-endian port bytes as
in the checker, and write

```
B=590069, beta=2^B−1, K=K0, HP=MF−beta,
J=1, q=beta+1, b=beta,
C=beta−MC, F=q−HP, alpha=q−F−C=MC+HP−beta,
omega=C, G=b*(q−F)+alpha,
R=G*(q²−1)+MC+q*MF, N=(R−1)/2.
```

The checker verifies `0<MC<beta`, `0<HP<beta`, and `0<alpha<beta`; hence
C, F, alpha and omega are positive and `C=q−F−alpha`. It computes exactly

```
R mod 4=3,   bit_length(R)=2360161,
popcount(N)=1770208=3*B+1,   R>=2*B.
```

Define the following finite integers symbolically:

```
X=2^R, Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q², w=X/q.
```

The reviewed central-binomial valuation in
`../current14-carrier64-pell-floor/` gives
`v2(Y)=popcount(N)−1=3B`, so s is a positive integer. All powers and sums are
finite, but far too large to expand.

## Full proposed Pell completion

Using `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`, set

```
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), D0=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta, ell=m*k,
gamma0=(D0−X−a*c)/H,
gamma=gamma0−w+(k−R−1)/U,
sigma_prime=ell+k+s+tau.
```

The reviewed floor bounds yield `Y<c/k<Y+1`, so eta and zeta are positive.
The first Pell congruence gives `E|(k−R−1)` and `k>=R+1`; since
`R>=2B`, `U|E`. The trace identity yields `gamma0>=2^(R−2)>w`, so gamma is
a positive integer. The positive first input is `sigma_prime`; with
`M=q³*b`, the literal graph has

```
Z=M*(ell+k−sigma_prime)+Y*b=−M*tau,
```

and A0 is zero. The main shift is `U*gamma0`, so `Dstar=U*D0` and A1 is
zero. The guard vanishes by omega=C.

The final inputs use the same independently reviewed strong and auxiliary
construction as `../ordinary13-folded-root86-toy-full-zero/`:

```
f+L*sqrt(Delta)=(D0+c*sqrt(Delta))^c,
i=Delta*L/c²,
S=Delta*L, V=chi_S(R)/S, y=psi_S(R),
T=(V+c+f²*R)/(c*f²), u=y−V.
```

Because `R=3 mod 4`, the cited binomial and Chebyshev arguments give
positive integers f, i, T and u and zero strong and auxiliary residuals.
Thus the proposed tuple has all fourteen positive inputs and all five
residuals zero. The checker only establishes finite seed/graph facts; the
unbounded completion is explicitly subject to independent review.

## The omitted transport congruence fails

For the inherited parent, the first norm requires `b|Bt`, where
`Bt=C*(X+K*q)−F*q`. Since `q=2^B` and `X=q*w`,

```
Bt mod b = (C*(K+w)−F) mod b,
w mod b = 2^((R−B) mod B).
```

The checker evaluates this residue exactly from the port bytes. Its
representative is nonzero, has 590003 bits and big-endian SHA-256
`ce55ad184bb41a6cd4d218547b8c3b4950fa42aba22e127057bd2ebbff092f95`.
Consequently the cited parent first norm cannot vanish with these scalar
coordinates.

In fact, conditional on the existing parent calibration theorem, no positive
parent zero can have **the same q and rank R**, even with the other inputs
changed. The reviewed 88/30-to-free-J unit argument and `FreeJ13Halt.forward`
first give the positive 12-input literal zero with the same q, R and X′.
This preservation is read from the explicit witness in the proof body of
`FreeJ13Halt.forward`; its existential theorem statement alone does not
expose those coordinate equalities. `FreeJPowerFinish.graph_power` then gives `X′=2^R` under its IΣ₁-model and
port-bound hypotheses; in the standard naturals this fixes X′ to the X above. The same q
and fixed beta force J=1, and the rank formula then fixes G. If a parent uses F′=F+d, equality of G forces
`alpha′=alpha+b*d` and `C′=C−q*d`. Since `0<alpha<b` and `0<C<q`, positive
alpha′ and C′ force d=0. Every positive parent zero has C′>0 and requires
b|Bt, which the computed residue excludes. This fixed-q,R obstruction is not
an unrestricted parent-zero nonexistence result.

## Degree and reproduction

The checker reconstructs the graph delta, verifies topology/liveness, pins
both coefficient bindings and payloads, computes the actual scalar facts and
runs a direct modular ray. The guard has degree at most 1, its square degree
at most 2, and the inherited four residuals have degree at most 13; the ray
has degree 26 with its nonzero leader recorded in `result.json`. These finite
controls do not replace the unbounded Pell argument.

```
python3 -I -S -B research/ordinary14-c-guard82-probe/check.py > /tmp/c-guard82.json
cmp /tmp/c-guard82.json research/ordinary14-c-guard82-probe/result.json
```

Independent mathematical review is recorded in
`../../reviews/ordinary14-c-guard82-probe-math-independent/`.
A separate independent decoder review is recorded in
`../../reviews/ordinary14-c-guard82-probe-independent/`.
