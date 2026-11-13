# Weighted projection excludes a large-q scalar family

This is an ordinary-integer conditional argument, not yet checked in Lean. Consider the [scalar family](../trace74-n5-r7-scalar-family/README.md) with `q≥256`, `m≥1`, `a=2q²m`, `X=a³`, `Y=a²/2`, `h=q−1`, and `H=4Y(X+1)−1=2a⁵+2a²−1`. The graph-derived weighted projection would require

```text
H | h X(X−128)(128X+1).
```

Put `M=4Y=2a²`, `g1=2a²−1`, `g2=258a²−1`, `g3=127a²−64`. Since `MX=H+1−M`, multiplying the projected product by `M³` and reducing modulo `H` yields `−2h g1 g2 g3`. `H` is odd, so the projection implies `H|h g1 g2 g3`.

The checker verifies exact integer-polynomial Bézout identities showing `g1` has inverse modulo `H`, and `g2` and `g3` have respective multiples congruent to `281370820607` and `4292918913` modulo `H`. Thus the projection implies

```text
H | hK,  K = 1207902117350120440191.
```

But `H>64q¹⁰`, while `64·256⁹>K`; hence `H>qK>hK>0`, impossible for a positive divisor. Therefore **this particular scalar family** cannot satisfy the graph projection for any `q≥256`. The conclusion does not exclude other `n=5,r=7` tuples and does not prove a graph theorem or fixed-BFS behavior.

Run `python3 -I -S -B research/trace74-n5-r7-family-projection-obstruction/check.py` from `Computability/DiophantineConsistency`. The checker records the exact projection identity, all three Bézout identities, and the numerical threshold; the receipt pins its output and negative controls.

The [independent arithmetic audit](../../reviews/trace74-n5-r7-family-projection-obstruction-independent/README.md) passed, including the divisibility cancellations and strict size comparison. No general graph or index exclusion follows from this family-specific result.
