# Conditional `n=4, r=7` scalar obstruction

This is an exact ordinary-integer polynomial certificate, not yet a Lean theorem or a graph exclusion. Let `q≥32`, `x≥32`, `Y≥1`, `t=2Y`, and suppose `q|x` and `q|Y`. Define

```text
B = x³+6x²+15x                   z = t(x+1)+2
c = z⁶−5z⁴+6z²−1                 kY = x³t⁷+6x²t⁵+10xt³+4t
k = 2x³t⁶+12x²t⁴+20xt²+8.
```

The displayed expressions for `k` and `kY` agree since `t=2Y`. They cannot satisfy `kY<c<k(Y+1)`:

1. Set `x=32+u,t=1+v` with `u,v≥0`. The checker expands
   `P=(c−kY−k)−x³t⁶(B+18−t)` and verifies that all 39 coefficients are positive. Hence `t≤B+18` implies `c>k(Y+1)`, contradicting the upper strict inequality.
2. Set `x=32+u,t=B+22+w` with `u,w≥0`. The checker expands `kY−c` and verifies all 113 coefficients are positive. Hence `t≥B+22` contradicts `kY<c`.
3. Thus `18<t−B<22`. Since `q|x` gives `q|B` and `q|Y` gives `q|t`, the positive integer `t−B` is a multiple of `q≥32` but is less than `q`, a contradiction.

The source uses unbounded exact integer polynomial arithmetic, with no external packages. Run `python3 -I -S -B research/trace74-n4-r7-scalar-obstruction/check.py` from `Computability/DiophantineConsistency`. It rejects non-isolated or optimized execution. The receipt records the actual output, hashes, and negative controls.

The Pell-ordinate identities, the interval inequalities, and the divisibility facts must still be bound to the **same actual graph witness** in Lean. The result does not itself establish a graph theorem, fixed-BFS behavior, 74/75 equivalence, or an iPRA endpoint.

The [independent arithmetic audit](../../reviews/trace74-n4-r7-scalar-obstruction-independent/README.md) passed; it independently checks both expansions and the conditional divisibility contradiction, without a Lean or graph claim.
