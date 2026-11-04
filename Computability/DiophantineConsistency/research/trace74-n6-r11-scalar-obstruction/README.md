# Conditional `n=6,r=11` scalar obstruction

This is an ordinary-integer polynomial certificate, not yet checked in Lean. Let `q≥260`, `X≥32`, `Y≥1`, `t=2Y`, and assume `q|X` and `q|Y`. Put `B=X⁵+10X⁴+45X³+120X²+210X`, `d=Xt²+2`, `z=t(X+1)+2`, and define `y₀(a)=0`, `y₁(a)=1`, `yₙ₊₁(a)=a yₙ(a)−yₙ₋₁(a)`. Set `k=2y₆(d)`, `kY=t y₆(d)` and `c=y₁₁(z)`.

For `X=32+u,t=1+v`, the checker verifies that all 105 coefficients of `(c−kY−k)−X⁵t¹⁰(B+250−t)` are positive. For `X=32+u,t=B+260+w`, it verifies all 397 coefficients of `kY−c` are positive. Consequently `kY<c<k(Y+1)` implies `250<t−B<260`. The positive integer `t−B` is a multiple of `q≥260`, but less than `q`: contradiction.

Run `python3 -I -S -B research/trace74-n6-r11-scalar-obstruction/check.py` from `Computability/DiophantineConsistency`; the receipt records output and negative controls. This scalar result has no Lean or graph binding; it does not by itself exclude other n6 cases, decide fixed ports, establish 74/75 equivalence or an iPRA endpoint.

The [independent arithmetic audit](../../reviews/trace74-n6-r11-scalar-obstruction-independent/README.md) passed both expansions and the conditional divisibility argument. It does not establish Lean or graph binding.
