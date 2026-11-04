# The weighted projection excludes one scalar family

For an ordinary integer `q ≥ 32`, set `Y=q³`, `X=8Y³`, `h=q−1`,
`H=4Y(X+1)−1=32Y⁴+4Y−1`, and take the odd index `r=5`. The weighted
projection would require

```
H | h·X·(X−32)·(32X+1).
```

That divisibility is impossible throughout this family. `H` is odd and
coprime to `X`, because `H ≡ −1 (mod Y)` and `X=8Y³`. Also
`gcd(H,h) | 35`: `h | Y−1` and `H−35` is divisible by `Y−1`.

The checker verifies the following exact polynomial identities:

```
H − 32Y(Y³−4) = 132Y−1
132³(Y³−4) − (132Y−1)((132Y)²+132Y+1) = −9,199,871
8H − Y(256Y³+1) = 31Y−8
31³(256Y³+1) − 256(31Y−8)((31Y)²+8·31Y+64) = 160,863.
```

Since `H` is odd, its gcd with `X−32=8(Y³−4)` divides 9,199,871;
its gcd with `32X+1=256Y³+1` divides 160,863. Repeated cancellation by
gcds in the displayed projection divisibility would therefore imply
`H | 35·9,199,871·160,863 = 51,797,159,703,555`. Yet
`H ≥ H(32³) = 36,893,488,147,419,234,303`, so this is impossible.
The checker verifies the symbolic identities and that every coefficient of
`H((32+u)³)−51,797,159,703,555` is positive. It also checks the `q=32`
instance and hashes/snippets of the source definitions and projection theorem.

This is an **external integer argument about this particular scalar family**.
It does not prove the general `n=4, r=5` case, establish a 74 graph zero,
formally bind the pinned source text to the selected Lean objects, or close the
guard or iPRA endpoint. The checked graph projection is conditional on a
positive 74 graph zero and its stated model assumptions.

Run `python3 -I -S -B research/trace74-family-projection-obstruction/check.py`
from `Computability/DiophantineConsistency`.

The [independent audit](../../reviews/trace74-family-projection-obstruction-independent/README.md)
passed, including the optimized-execution rejection controls.
