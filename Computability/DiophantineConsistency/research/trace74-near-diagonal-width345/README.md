# Conditional wider near-diagonal obstruction

This note gives an **ordinary-integer** argument for three wider regions of
the trace74 index plane. The [width-three case](../trace74-width3-graph-join/README.md)
has subsequently been checked in Lean for the stated same-zero hypotheses;
the width-four and width-five cases below have not been formalized as model
theorems. None is a reverse-guard proof or an iPRA endpoint.

Fix `c` in `{3, 4, 5}`. Let integers `q, h, X, Y, n, r` satisfy

```text
q ≥ 2^30,  0 < h < q,  Y ≥ q^3,  X ≥ 2,
n ≥ 4c,    1 ≤ r ≤ n+c.
```

Put `t=2Y`, `K=2^r`, and define `y_0(z)=0`, `y_1(z)=1`,
`y_(i+1)(z)=z*y_i(z)-y_(i-1)(z)`. Assume the strict Pell gap

```text
t*y_n(X*t^2+2) < y_r(t*(X+1)+2)                            (1)
```

and the **same tuple's** projection divisibility

```text
H | h*X*(X-K)*(K*X+1),     H=4Y*(X+1)-1.                  (2)
```

These conditions are inconsistent. The thresholds below use the cubic bound
`Y≥q³`; this argument does not establish them from the weaker `Y≥q²` alone.
Thus the explicit width/index pairs are
`c=3, n≥12`; `c=4, n≥16`; and `c=5, n≥20`. They exclude the
corresponding near-diagonal region only when all the displayed assumptions
have been established for the same graph valuation.

## Pell gap and a height lower bound

For positive indices and `u≥1`, the recurrence and monotonicity give
`y_i(u+2)≥u^(i−1)`. For `z≥2`, it also gives `y_i(z)≤z^(i−1)`.
Since `t*(X+1)+2≤2Xt`, (1) and `r≤n+c` imply

```text
X^(n−1) t^(2n−1) < (2Xt)^(n+c−1),
Y^(n−c) < 2^(2c−1) X^c.                                  (3)
```

All cancelled factors are positive, and `n−c` is nonnegative. If
`X≤8hK²Y²`, (3), multiplication by positive factors, and cancellation of
`Y^(2c)` yield

```text
Y^(n−3c) < 2^(5c−1) h^c K^(2c).                          (4)
```

We show that the opposite strict inequality follows from the size bounds.
Let `d=n−4c≥0` and `P=2^d`. Then `n−3c=d+c`, and

```text
Y^d ≥ (2^(2c))^d = P^(2c),
K ≤ 2^(d+5c) = 2^(5c) P,
Y^c ≥ q^(3c) > 2^(5c−1+10c²) h^c.                       (5)
```

The first line uses `Y≥q³≥2^(2c)`, and the strict last inequality follows
from `h<q`, `q≥2^30`, and the finite comparison

```text
60c > 5c−1+10c²,   c ∈ {3,4,5}.
```

Indeed, `q^(2c)≥2^(60c)>2^(5c−1+10c²)` and `q^c>h^c`.
Multiplying the first and last inequalities in (5), and using the middle
one, gives

```text
Y^(n−3c) > 2^(5c−1) h^c K^(2c),
```

contradicting (4). Therefore

```text
X > 8hK²Y².                                                (6)
```

## Projection contradiction

Because `r≥1` and the other assumptions include `n≥12`, the relevant graph
application has `r≥2`; for this integer argument explicitly assume `r≥2`
when applying (2). In fact, if (1) holds, `r≥2` follows: the left side is
positive and `y_1=1`, while `t≥2`. Set `L=K/4`, an integer at least one,
and define

```text
a=4Y−1,  b=4(K+1)Y−1,  e=(K−1)Y−L,  S=h*a*b*e.
```

The exact polynomial identities in the independently checked
[near-diagonal packet](../trace74-uniform-near-diagonal-height/README.md)
and `gcd(H,4)=1` turn (2) into `H | S`. All factors are positive, and

```text
0 < S < 32hK²Y³ < 4XY < H,
```

where the middle inequality uses (6). A positive integer divisible by `H`
cannot be less than `H`, giving the contradiction.

The bound (6) and the final comparison require no parity assumption on
`r`. Formalization in a nonstandard model would require represented
variable-index power and Pell bounds, discrete ordered-ring reasoning, and
same-valuation bindings. For each fixed `c`, (5) can avoid multiplying two
variable exponents: expand the constant `2c`, use addition of the fixed
exponent `5c`, and apply multiplication-of-bases to
`(2^(2c))^d=(2^d)^(2c)`. The companion `check.py` checks only the finite
constant comparisons and exponent bookkeeping; it is not a proof of (1),
(2), the analytic inequalities, or their applicability to a graph zero.
The [independent arithmetic review](../../reviews/trace74-near-diagonal-width345-independent/README.md)
applies to the earlier hash-pinned revision; the later opening paragraph
records the separate width-three Lean result.
