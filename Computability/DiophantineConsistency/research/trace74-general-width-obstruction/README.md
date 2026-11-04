# A general fixed-width near-diagonal obstruction

This is an ordinary-integer argument extending the previously reviewed
widths 3, 4 and 5. A subsequent [Lean model theorem](../trace74-variable-width-index-client/README.md)
checks a related same-zero criterion at arbitrary internal widths, with
explicit threshold assumptions and the stronger condition `3c+1≤n`.
Neither result proves the 74-operation reverse guard. The graph applicability
and fixed-symbolic specialization retain their stated same-tuple facts.

Let integers `B≥1`, `c≥1`, `n`, `r`, `q`, `h`, `X`, and `Y` satisfy

```text
q ≥ 2^B,  0 < h < q,  Y ≥ q^3,  X ≥ 2,
n ≥ 3c,  1 ≤ r ≤ n+c,
2c < 3B,
(3B−2c)n > (10B+5)c + 2c² − 1.                         (A)
```

Put `t=2Y`, `K=2^r`, `H=4Y(X+1)−1`, and let the Pell ordinates be
`y_0(z)=0`, `y_1(z)=1`, `y_(j+1)(z)=z*y_j(z)−y_(j−1)(z)`. Assume
both facts for the **same** quantities:

```text
t*y_n(X*t²+2) < y_r(t*(X+1)+2),                          (P)
H | h*X*(X−K)*(K*X+1).                                   (D)
```

These assumptions contradict one another. No assumption `n<r` or parity
of `r` is needed. The strict gap implies `r≥2`: its left side is at least
`t≥2`, whereas the first ordinate is `1`.

## Proof

The recurrence gives `y_i(u+2)≥u^(i−1)` for `u≥1` and `i≥1`, and
`y_i(z)≤z^(i−1)` for `z≥2`. As `t(X+1)+2≤2Xt`, the gap and
`r≤n+c` imply

```text
X^(n−1)t^(2n−1) < (2Xt)^(n+c−1),
Y^(n−c) < 2^(2c−1) X^c.                                 (1)
```

From (D), write `L=K/4` and use the exact projection identities in
[`trace74-uniform-near-diagonal-height`](../trace74-uniform-near-diagonal-height/README.md).
Because `r≥2`, `L` is a positive integer. They give `H | S` for
`S=h(4Y−1)(4(K+1)Y−1)((K−1)Y−L)`, with
`0<S<32hK²Y³`. Therefore `H≤S` and, since `4XY<H`,

```text
X < 8hK²Y².                                               (2)
```

Substituting (2) in (1), then cancelling `Y^(2c)` using `n≥3c`, yields

```text
Y^(n−3c) < 2^(5c−1) h^c K^(2c)
          < 2^(2cn+2c²+5c−1) q^c.                        (3)
```

The second inequality uses `h<q` and `K≤2^(n+c)`. By rearranging (A),

```text
B(3n−10c) > 2cn+2c²+5c−1 ≥ 0.                            (4)
```

Hence `3n−10c>0`. From `Y≥q³`, (3), and cancellation of `q^c`,

```text
q^(3n−10c) < 2^(2cn+2c²+5c−1).
```

But `q≥2^B` and (4) give a strictly larger lower bound, a contradiction.
All exponents cancelled above are nonnegative and all bases are positive.

## Examples and scope

For `B=30`, the condition `2c<3B` allows `c≤44`; the smallest `n`
certified by (A) (also requiring `n≥3c`) is 12, 16, 20 and 8646 for
`c=3,4,5,44`, respectively. For `c=6` it is 25. These are sufficient
thresholds, not claims of optimality.

The Lean symbolic parameter is `betaNat=2^(67*8807)−1`, and existing
`CompactFixedBeta.beta_identity` identifies `(betaNat:V)+1` with the
represented exponential at `67*8807=590069`. For an ordinary positive
`J`, the tuple equation `q=betaNat*J+1` gives `q≥2^590069`. Substituting
`B=590069` permits fixed widths up to `c=885103` at sufficiently large
`n`. The enormous numeral need not be expanded to state the corresponding
model inequality: represented exponentiation and the symbolic identity
are the appropriate interfaces. A separate [Lean model lemma](../trace74-fixed-q-symbolic-bound/README.md)
now derives this represented lower bound on `q` from the symbolic first
port and a positive first witness. The [direct-index model theorem](../trace74-variable-width-index-client/README.md)
also supplies a conditional general-width exclusion; it does not cover the
`n=3c` boundary. The symbolic port is not connected to an external payload
by those lemmas.

The preceding computation excludes only widths bounded by the stated
constant. It does not cover arbitrary gaps `r−n`, prove absence of graph
zeros, or establish the reverse guard or the iPRA endpoint. A model proof
would need represented-power inequalities and cancellation, the
variable-index arithmetic behind (A), and a same-valuation join. In
particular, the factor `2cn` involves a product of model indices when `c`
is variable; an ordinary integer proof does not provide that induction.

Run `python3 -I -S -B research/trace74-general-width-obstruction/check.py`
from the `Computability/DiophantineConsistency` directory. The checker
verifies example thresholds and constant bookkeeping only; it does not
prove the universal inequalities or the graph assumptions.
The [independent arithmetic review](../../reviews/trace74-general-width-obstruction-independent/README.md)
applies to the earlier hash-pinned version of this note; the updated
opening and links above record the separate Lean model bounds.
