# Negative-rank scalar diagnostic with a failed graph projection

This exact ordinary-integer diagnostic combines more of the individually checked scalar, Pell and congruence facts than the separate [n=4 scalar family](../trace74-n4-scalar-pell-witness/README.md). It **is not a 74 graph zero**: it explicitly fails a separately checked necessary graph projection. It also does not use the retained fixed-BFS tuple.

Take `q=32`, `beta=31`, `J=1`, `MC=1`, `MF=32`, `Y=q³`, `X=8Y³`, `n=4`, `r=5`, and derive `k,c,eta,zeta` from the two Pell ordinates as in the linked scalar family. Set `D=q²−1`, `M=(MC+q MF)J`, `t=975595108`, `R=−(5+t c)`, `F=1`, and `C=q²−qF−(R−M)/D`. The quotient is exact and `C>0`.

The checker verifies the natural-port bounds, `n<r<2n` with odd `r`, both ordinate equations and positive `eta,zeta`, `q|X`, `q³|Y`, `c>2q⁴`, the actual scalar rank formula `R=(q(q−F)−C)(q²−1)+M`, the signed upper bound, `q⁴ | R+1−k`, and `|R| ≡ r (mod c)`. Thus those selected scalar conditions do not imply nonnegative rank. They do not include all conditions of the 74 graph.

In particular, with `h=beta J`, `A=Y(X+1)` and `H=4A−1`, the checked graph projection would require

```text
H | (h X)(X−2ʳ)(2ʳX+1).
```

The diagnostic evaluates `H=36893488147419234303` and finds that divisibility **fails**, with gcd 3. This is direct evidence that the graph projection is an additional constraint which could exclude the example and is not a counterexample to a graph theorem. The scalar `MC,MF` and beta are not the fixed-BFS coefficient tuple.

Run `python3 -I -S -B research/trace74-n4-negative-rank-scalar/check.py` from `Computability/DiophantineConsistency`. It rejects missing isolation/no-site flags and optimized Python. The receipt records source and output hashes. The [independent arithmetic audit](../../reviews/trace74-n4-negative-rank-scalar-independent/README.md) reproduced the selected scalar facts and the failed projection. No Lean model claim or general normalization result is made.
