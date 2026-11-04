# Conditional near-diagonal projection obstruction

This note presents an ordinary-integer argument and exact sparse-polynomial checks. A subsequent [Lean model theorem](../trace74-near-diagonal-graph-join/README.md) now excludes the stated **near-diagonal branch** for the same positive graph zero at `q≥2³⁰` and `n≥8`, with both ordinate equations supplied. It does not establish the reverse guard, index equality, 74/75 equivalence, or an iPRA endpoint.

Let integers `q>=2^30`, `h=q-1`, `Y>=q^3`, `X>=32`, `n>=8`, and odd `r>=3` satisfy `r<=n+2`. Put `t=2Y`, `K=2^r`, `L=K/4`, `H=4Y(X+1)-1`, and use `y_0(z)=0`, `y_1(z)=1`, `y_(i+1)(z)=z*y_i(z)-y_(i-1)(z)`. Assume separately:

1. the strict Pell gap `t*y_n(X*t^2+2)<y_r(t*(X+1)+2)`;
2. the weighted projection `H | h*X*(X-K)*(K*X+1)`.

Under these assumptions there is a contradiction. The graph-side facts, especially the **additional** window `r<=n+2`, must be supplied; the currently checked general index window only gives `n<r<2n`.

For the height estimate, `y_i(u+2)>=u^(i-1)` for integers `u>=1`, `i>=1`, by induction using the recurrence and `y_(i-1)<=y_i`; likewise `y_i(z)<=z^(i-1)` for `z>=2`. Since `t*(X+1)+2<=2Xt`, the gap and `r<=n+2` yield

```text
X^(n-1) t^(2n-1) < (2Xt)^(n+1),
t^(n-2)<2^(n+1)X^2, hence Y^(n-2)<8X^2.
```

`K<=2^(n+2)`, and the size hypotheses give `Y^(n-6)>512h^2 K^4`: indeed `Y^(n-6)>=q^(3n-18)`, `h<q`, and `q^(3n-20)>=2^(30(3n-20))>2^(4n+17)>=512K^4`. The strict exponent difference is `30(3n-20)-(4n+17)=86(n-8)+71>0`. Combining with the Pell gap and cancelling positive powers gives

```text
X > 8h K^2 Y^2.
```

For the projection, write `a=4Y-1`, `b=4(K+1)Y-1`, `d=(K-1)Y-L`. The checker expands the identities

```text
(4Y)^3 hX(X-K)(KX+1) = h(H-a)(H-b)(KH-4d),
(H-a)(H-b)(KH-4d)+4abd
  = H[KH^2-KH(a+b)+Kab-4dH+4d(a+b)].
```

The projection therefore yields `H | 4habd`. As `H=4Y(X+1)-1`, `gcd(H,4)=1`, so `H|S` for `S=habd`. All factors are positive, and `S<32hK^2Y^3`; but `H>4XY>32hK^2Y^3`, contradiction. This uses no assertion `Lh<Y` and does not identify the divisor quotient.

The [variable-parameter Lean reduction](../trace74-uniform-projection-reduction-draft/README.md) proves this divisibility consequence in any commutative ring when `K=4L`, assuming the weighted projection. It does not establish the actual graph premise or the other inequalities in this argument.

For a nonstandard model of `IΣ₁`, this integer argument is not automatically a proof. The existing [`ArithmeticHalfBinomialSandwich.lean`](../../Lean/DiophantineConsistency/ArithmeticHalfBinomialSandwich.lean) proves both model-indexed Pell bounds by represented induction: `power (2*b+3) j ≤ ycoord (j+1) b ≤ power (2*(b+2)) j`. [`ArithmeticPow.lean`](../../Lean/DiophantineConsistency/ArithmeticPow.lean) supplies represented variable-base power, addition, and monotonicity laws. A [captured-provider Lean author check](../trace74-near-diagonal-pell-model/README.md) instantiates those sandwich bounds for the specific 74-operation Pell bases and derives the corresponding strict power gap. The original graph index window alone does not discharge `r<=n+2`.

Subsequent captured-provider Lean checks have supplied the [same-zero Pell gap](../trace74-pell-gap-binding/README.md), the [model-indexed bound `Y^(n-2)<8X²`](../trace74-near-diagonal-height-model/README.md) under the near-diagonal window, and the [same-zero reduced projection](../trace74-uniform-projection-graph-draft/README.md). An [ordered-ring contradiction](../trace74-uniform-height-contradiction-draft/README.md) and its [same-zero graph client](../trace74-uniform-graph-height-draft/README.md) rule out a supplied ordinate under the stronger bound `X>8hK²Y²`. The [amplification lemma](../trace74-near-diagonal-large-height-model/README.md) derives that bound from the two displayed power inequalities, and the [lower power theorem](../trace74-near-diagonal-size-model/README.md) derives the second inequality from the stated size and index bounds. The [same-zero join](../trace74-near-diagonal-graph-join/README.md) combines them to exclude `r≤n+2` when `n≥8` and `q≥2³⁰`. Indices outside that window remain open. These author checks do not authenticate their complete provider ancestry.

`python3 -I -S -B research/trace74-uniform-near-diagonal-height/check.py` checks the exact free-polynomial identities, the affine exponent comparison, and one strict-gap numerical example; it does not exhaustively verify the universal inequalities or invoke Lean. The invocation guard rejects Python optimization because the checker uses assertions. The numerical example has no asserted graph projection.

The [independent arithmetic audit](../../reviews/trace74-uniform-near-diagonal-height-independent/README.md) verified the conditional integer argument in the earlier, hash-pinned revision of this note. The later paragraph reporting the captured-provider Lean author check is outside that audit.
