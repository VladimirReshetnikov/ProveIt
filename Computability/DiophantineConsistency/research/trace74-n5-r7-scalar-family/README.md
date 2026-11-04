# Conditional `n=5, r=7` scalar family

This exact ordinary-integer certificate has not been checked in Lean. For arbitrary integers `q≥32` and `m≥1`, take `a=2q²m`, `Y=a²/2=2q⁴m²`, `X=a³`, and `t=2Y=a²`. Then `a≥256`, `q|X`, `q³|Y`, and `5<7<10`. With `y₀(d)=0`, `y₁(d)=1`, `yₙ₊₁(d)=d yₙ(d)−yₙ₋₁(d)`, define

```text
d = Xt²+2 = a⁷+2         z = t(X+1)+2 = a⁵+a²+2
k = 2y₅(d)               kY = t y₅(d)        c = y₇(z).
```

Substituting `a=256+u`, the checker verifies all 28 coefficients of `c−kY` and all 29 coefficients of `kY+k−c` are positive. It also verifies `y₅(d)>1`, so `kY=t y₅(d)>a²=4q⁴m²≥4q⁴>2q⁴`. Thus every such scalar tuple has `kY<c<k(Y+1)` and `c>2q⁴`. This shows those selected scalar conditions alone do not exclude the index pair `n=5,r=7`, even with a prescribed positive `q`.

The checker separately evaluates the original sample `q=32,a=256`, which **fails** the independently checked necessary weighted graph projection: for `h=q−1` and `H=4Y(X+1)−1`, the remainder of `hX(X−128)(128X+1)` modulo `H` is `1648680914823`, with `H=2199023386623`. This certificate does not decide projection for the general family. The scalar family is not shown to be a graph zero, does not provide the other fixed-BFS ports, and does not settle the fixed-BFS guard or the `n=5` branch.

Run `python3 -I -S -B research/trace74-n5-r7-scalar-family/check.py` from `Computability/DiophantineConsistency`; the receipt records source/output hashes and negative controls.

The [independent arbitrary-q audit](../../reviews/trace74-n5-r7-scalar-family-arbitrary-q-independent/README.md) passed. It checks the scalar argument and separate sample only; no general projection or graph claim follows.
