# A q² Y-quotient probe and proposed actual-port zero

This **78-operation, 14-positive-input, degree-50** graph is a provisional
probe, not a new consistency equation. It replaces the reviewed 79/60
graph's `Y=q³*s` by `Y=q²*s`, deleting the sole q³ gate. The forward
positive-zero map is immediate (`s_new=q*s_old`), but the reverse would need
to recover `q|s_new`. The construction below proposes an actual-compact44
positive zero with `q³` not dividing Y. It is submitted for independent
review. It does not settle unrestricted positive-zero equivalence or parent
existence at other coordinates, prove a zero of the displayed PDF equation,
or give a Lean/iPRA theorem.

## Exact scalar seed

The checker authenticates the P72 and P115 compact44 port bytes and verifies

```
B=590069, beta=2^B−1, q=beta+1, J=1, e=439547,
F=(K0+2^e) mod beta, C=1, alpha=beta−F,
G=beta*(q−F)+alpha,
R=G*(q²−1)+MC+q*MF, N=(R−1)/2.
```

It checks `0<F<beta`, so alpha is positive and `C=q−F−alpha=1`, and it
computes

```
R mod B=e, R mod 4=3, R>=2B, bit_length(R)=2360276,
popcount(N)=1770128=3B−79.
```

Put

```
X=2^R, w=X/q=2^(R−B),
h=(X+K0−F)/beta.
```

Since `R mod B=e`, `w=2^e (mod beta)` and `X=q*w=w (mod beta)`, so the
numerator defining h is divisible by beta. It is positive because
`X>=q²>F` and `K0>=0`. The residue guard
`C*(X+K0)−F−beta*h=0` therefore vanishes.

## Proposed full Pell witness

Define

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q², E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q².
```

The reviewed binomial valuation gives

```
v2(Y)=popcount(N)−1=3B−80.
```

Hence s is positive and integral, while `q³` does **not** divide Y.
The exact integer Y is unexpanded. With Pell coefficients
`(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`, put

```
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), D0=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(D0−X−a*c)/H,
gamma_prime=gamma0+(k−R−1)/U.
```

Set the direct first-root input to tau. The reviewed floor estimates give
positive eta and zeta, while the first Pell congruence gives
`E|(k−R−1)` and `k>=R+1`. As `R>=2B`, `U|E`, so gamma_prime is a positive
integer. The trace identity gives `gamma0>0`. The first Pell norm makes the
first residual zero, and the modified main carrier gives

```
Dstar=U*(X+a*c)+H*(U*gamma_prime−k+R+1)=U*D0,
```

so the main residual is zero.

For the remaining inputs use the same aligned-index strong/auxiliary
completion reviewed in `../ordinary13-folded-root86-toy-full-zero/`:

```
f+L*sqrt(Delta)=(D0+c*sqrt(Delta))^c,
i=Delta*L/c²,
S=Delta*L, V=chi_S(R)/S, y=psi_S(R),
T=(V+c+f²*R)/(c*f²), u=y−V.
```

The cited Pell/binomial and Chebyshev proofs use `R=3 mod4` and give positive
integer f, i, T and u, with both remaining residuals zero. Thus the seed
purports to satisfy all five squared residuals with fourteen positive inputs.
Its unbounded proof is under review; the checker confirms only finite seed,
graph and degree facts.

## What this does and does not exclude

The same Y cannot occur at a 79-graph zero, because that graph has
`Y=q³*s_old` with positive integer s_old. More strongly, a parent zero at
the **same q and R** would, subject to the existing source-level calibration
and its rank-window hypotheses, have `X=2^R` and the same unique binomial Y
by `../current14-carrier64-pell-floor/`. Here `q>=16`, `R>=26`, and
`R+1<X*Y` hold, so that Y is the one above and is not divisible by q³. This
fixed-q,R exclusion relies on replaying the reviewed parent coordinate maps
and calibration; it is not a proof that the parent has no zero at other
q,R, nor an unrestricted nonequivalence theorem.

## Graph and degree

The checker verifies the exact single-gate deletion and all liveness, and
checks 100 signed controls for the forward substitution `s_new=q*s_old`.
With `Y=q²*s`, `deg(Y)<=3`, `deg(X)<=2`, `deg(U)<=5`, `deg(a)<=5`,
`deg(c)<=4`, `deg(H)<=5`, `deg(ell)<=9`, and `deg(R)<=4`. The direct
first residual has degree at most 18. Writing
`Dstar=U*a*c+Theta` with `Theta=U*X+H*(U*gamma−k+R+1)` of degree at most
11, the exact norm cancellation bounds A1 by degree 25. Auxiliary, strong
and guard degrees are at most 20, 18 and 3, so the output has degree at most
50. A direct all-inputs-equal ray at the authenticated ports has degree 50
and leading coefficient 538340853 modulo 1000000007, proving exact
specialized degree 50.

```
python3 -I -S -B research/ordinary14-q2-78-probe/check.py > /tmp/q2-78.json
cmp /tmp/q2-78.json research/ordinary14-q2-78-probe/result.json
```

The finite checker does not replace the unbounded Pell completion.

Independent mathematical review is recorded in
`../../reviews/ordinary14-q2-78-probe-math-independent/`.
