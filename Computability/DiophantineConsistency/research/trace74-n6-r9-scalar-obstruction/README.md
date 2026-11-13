# Conditional `n=6,r=9` scalar obstruction

This is an ordinary-integer polynomial argument, not yet checked in Lean. Let `X≥32`, `Y≥1`, `t=2Y`, `d=Xt²+2`, `z=t(X+1)+2`, with `y₀(a)=0`, `y₁(a)=1`, `yₙ₊₁(a)=a yₙ(a)−yₙ₋₁(a)`. Set `k=2y₆(d)`, `kY=t y₆(d)`, and `c=y₉(z)`.

If `X≤t−3`, write `X=32+u` and `t=X+3+w`, with `u,w≥0`. The checker verifies that every one of the 137 coefficients of `kY−c` is positive, contradicting `kY<c`. If `X≥t−2`, write `t=2+u` and `X=t−2+w=u+w`, with `u,w≥0`. Every one of the 115 coefficients of `c−kY−k` is positive, contradicting `c<kY+k=k(Y+1)`.

Thus the two strict inequalities would imply `t−3<X<t−2`, impossible for integers. The displayed certificate needs no q-divisibility or fixed-port assumption. It remains conditional: same-witness Pell ordinate and interval identities must be bound separately to an actual 74 zero in Lean. It does not exclude the `n=6,r=11` branch, prove a graph theorem, settle 74/75 equivalence, or establish an iPRA endpoint.

Run `python3 -I -S -B research/trace74-n6-r9-scalar-obstruction/check.py` from `Computability/DiophantineConsistency`; the receipt records exact output and negative controls.

The [independent arithmetic audit](../../reviews/trace74-n6-r9-scalar-obstruction-independent/README.md) passed both expansions and the discrete gap argument. It does not establish Lean or graph binding.
