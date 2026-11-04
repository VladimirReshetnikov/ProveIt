# Conditional large-q `n=5, r=7` projection obstruction

This is an ordinary-integer argument, not yet checked in Lean. Let `q≥2³⁰`, `X≥32`, `Y≥q³`, and `h=q−1`. Put `t=2Y`, `d=Xt²+2`, `z=t(X+1)+2`, and define `y₀(a)=0`, `y₁(a)=1`, `yₙ₊₁(a)=a yₙ(a)−yₙ₋₁(a)`. Assume the explicit scalar inequality

```text
t y₅(d) < y₇(z).
```

It implies the useful size bound `X>65532hY`:

1. `y₅(u+2)=u⁴+8u³+21u²+20u+5`, so `t y₅(d)≥X⁴t⁹`. Also `z⁶−y₇(z)=(z²−1)(5z²−1)≥0`, `z≤t(X+2)`, and the checker verifies `(X+2)⁶≤2X⁶` for `X≥32`. Therefore `X⁴t⁹<2X⁶t⁶` and `X²>4Y³`.
2. Since `Y≥q³`, `h<q`, and `4·2³⁰>65532²`, the preceding strict inequality gives `X²>(65532hY)²`, hence `X>65532hY`.

Assume separately the weighted projection `H | hX(X−128)(128X+1)`, where `H=4Y(X+1)−1`. With `g1=4Y−1`, `g2=516Y−1`, `g3=127Y−32`, the exact projection identity in the checker and the oddness of `H` imply `H|S`, where `S=h g1 g2 g3`. Write `S=jH`. Since all factors are positive,

```text
H>4YX>262128hY²,   S<262128hY³,
```

so `0<j<Y`. Also `0<32h<Y` follows from the q and Y bounds. Reducing `S=jH` modulo `Y` gives `j≡32h (mod Y)`, hence `j=32h`. Cancel `h>0`; then `g1g2g3=32H`. Reducing this equality modulo `4Y` gives `4Y|3Y`, impossible for `Y>0`.

The checker records the needed polynomial identities and constants using exact integer arithmetic. Run `python3 -I -S -B research/trace74-n5-r7-large-q-obstruction/check.py` from `Computability/DiophantineConsistency`; the receipt pins output and negative controls.

This is stronger than the [specific-family obstruction](../trace74-n5-r7-family-projection-obstruction/README.md), but it remains **conditional**: a graph theorem still requires the same witness to supply the scalar inequality, `Y≥q³`, large fixed-port `q`, and the weighted projection. No Lean, fixed-BFS graph, general index, 74/75 equivalence, or iPRA endpoint is asserted here.

The [independent arithmetic audit](../../reviews/trace74-n5-r7-large-q-obstruction-independent/README.md) passed, including strict growth and the quotient argument. It does not establish Lean or graph binding.
