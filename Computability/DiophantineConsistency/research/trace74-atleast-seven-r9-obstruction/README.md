# Conditional `n≥7,r=9` projection obstruction

This ordinary-integer argument has not yet been checked in Lean. Let `q≥64`, `X≥32`, `Y≥q³`, `h=q−1`, `t=2Y`, and define `y₀(a)=0`, `y₁(a)=1`, `yₙ₊₁(a)=a yₙ(a)−yₙ₋₁(a)`. Assume the scalar inequality

```text
t y₇(Xt²+2) < y₉(t(X+1)+2).
```

The checker verifies that `y₇(u+2)≥u⁶` for `u≥0`; that `z⁸−y₉(z)=(z²−1)((z²−1)(7z²−1)+1)+1≥0` for `z≥1`; and that `(X+2)⁸≤2X⁸` for `X≥32`. Since `t≥2`, `z=t(X+1)+2≤t(X+2)`, so the scalar gap implies `X⁶t¹³<2X⁸t⁸`, hence `X²>16Y⁵`. From `Y≥q³`, `h<q`, and `16·64⁷>1048572²` it follows that `X>1048572hY`.

Assume separately the weighted projection `H | hX(X−512)(512X+1)` with `H=4Y(X+1)−1`. The checker verifies the exact reduction giving `H|S`, with

```text
S=h(4Y−1)(2052Y−1)(511Y−128).
```

Writing `S=jH`, positivity and the growth bound give `0<j<Y` because `S<4·1048572 hY³` and `H>4·1048572 hY²`. Also `0<128h<Y`. Reduction mod `Y` gives `j≡128h (mod Y)`, hence `j=128h`. Cancel `h>0`; reducing the resulting equality mod `4Y` gives `4Y|3Y`, impossible.

For a same-tuple first index `n≥7`, the separately checked monotonicity of the first Pell ordinate and the graph's positive slack would supply the displayed scalar inequality; that model/graph binding is **not** part of this packet. The argument does not cover `n=6` (handled by a separate conditional scalar result), claim a Lean theorem, or settle 74/75 equivalence or an iPRA endpoint.

Run `python3 -I -S -B research/trace74-atleast-seven-r9-obstruction/check.py` from `Computability/DiophantineConsistency`; the receipt records output and negative controls.

The [independent arithmetic audit](../../reviews/trace74-atleast-seven-r9-obstruction-independent/README.md) passed the conditional growth, projection and quotient argument. It does not establish model/graph or Lean binding.
