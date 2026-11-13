# Independent positive auxiliary root: a 76-operation route

The 77 graph uses the positive witness `e` only in `y=V+e`, and subsequently
uses `y` only through `y²` in

```
Na = A*(V²-y²) + y²,       A = Delta*(f²-1),
V  = f²*(c*T-R) - c.
```

Replace `e` with a positive independent witness `y`, delete the `V+e` gate,
and retain the other gates. This is a proposed 76-operation graph. The
following graph-specific argument gives a route to both witness maps; it is
not yet a Lean theorem, generated-graph check, endpoint, or actual zero.

## A size lemma from the main and strong norms

For a positive zero of either graph, the sum of squares and the existing
negative-unit argument give `M=0`, `W=0`, `Lt=0`, and `Na=1`. The transport
zero supplies the positivity and bound hypotheses needed by the existing
`P64Root.main_root` after lifting the q-cube coordinate. In particular it
gives a natural `g` satisfying

```
g² = 1 + Delta*c²,  Delta = (a+2)²-1,
c = k*Y+eta,       k=eta+zeta,       Y=q³*s.
```

Every displayed witness is positive, so `c≥3`. Put `n=a+2`. We claim
`c≥2n`. If `2≤c<2n`, then `nc−1≥0` and

```
(nc−1)² < g² = (nc)²−c²+1 < (nc)².
```

The left inequality is equivalent to `c*(2n−c)>0`; the right follows from
`c≥2`. There is no integer strictly between the consecutive nonnegative
integers `nc−1` and `nc`, so these strict square bounds are impossible.
The same argument uses only ordered-ring arithmetic and discreteness, making
it a candidate for the repository's IΣ₁ model difference ring.

Consequently `Delta=n²−1<c²`. The strong residual `W=0` says
`Delta*(f²−1)=i²*c⁴` with positive `i`. If `f²≤c+1`, then

```
Delta*(f²−1) ≤ Delta*c < c³ < c⁴ ≤ i²*c⁴,
```

a contradiction. Thus **`f²>c+1`** at any such zero.

## New witness back to the old graph

With independent `y>0`, `Na=1` rewrites to

```
A*(y²−V²) = y²−1.
```

The strong equation gives `A=i²*c⁴≥2`; `y≥1` therefore implies
`V²≤y²`. Equality forces `y²=1` and `V²=1`. The only equality case that
could prevent `y−V>0` is `V=y=1`. But `V=1` gives
`f²*(c*T−R)=c+1`. Since the right side is positive and `f²>0`, the
integer factor `c*T−R` is positive and hence at least 1. It follows that
`f²≤c+1`, contradicting the size lemma. Hence `y−V>0` in the model
difference ring; representing that positive difference by a positive model
natural supplies `e`, with `V+e=y`. Every other residual and the output
then agree with the 77 graph on this witness.

## Old witness to the new graph

For a 77 zero, put `yold=V+e`. It cannot be zero: otherwise `Na=1` gives
`A*V²=1`, impossible in a discrete ordered ring because `A≥2` and any
nonzero integer square is at least 1. Represent `|yold|` by a positive model
natural and use it as the new witness. Its square equals `yold²`, and all
residuals and the output agree.

Both constructions keep the four ports and all other witnesses fixed. The
proposed argument depends on the graph's actual `M=0`, `W=0`, `Lt=0` and
`Na=1`; it does not assert either witness map for arbitrary valuations.
The main-root extraction, discrete inequalities, absolute-value construction,
and shifted graph identities still require explicit Lean composition and
verification. Degree and gate counts also require an external graph audit.
