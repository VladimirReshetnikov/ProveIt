# Conditional `n=5, r=9` scalar obstruction

This exploratory exact arithmetic certificate has not been checked in Lean. Let `q≥73`, `x≥32`, `Y≥1`, `t=2Y`, with `q|x` and `q|Y`. Write `B=x⁴+8x³+28x²+56x`, `d=xt²+2`, `z=t(x+1)+2`, and define polynomials `y₀(a)=0`, `y₁(a)=1`, `yₙ₊₁(a)=a yₙ(a)−yₙ₋₁(a)`. Set `k=2y₅(d)`, `kY=t y₅(d)`, and `c=y₉(z)`.

For `x=32+u,t=1+v`, the checker verifies all 68 coefficients of `(c−kY−k)−x⁴t⁸(B+68−t)` are positive. For `x=32+u,t=B+73+w`, it verifies all 226 coefficients of `kY−c` are positive. Therefore `kY<c<k(Y+1)` gives `68<t−B<73`; the positive integer `t−B` is divisible by `q≥73`, a contradiction.

Run `python3 -I -S -B research/trace74-n5-r9-scalar-obstruction/check.py` from `Computability/DiophantineConsistency`. This is an ordinary-integer scalar statement. Its recurrence expressions, divisibility, and both inequalities have not been bound to a graph zero; it does not settle `n=5,r=7`, unrestricted indices, 74/75 equivalence, or an iPRA endpoint.

The [independent arithmetic audit](../../reviews/trace74-n5-r9-scalar-obstruction-independent/README.md) passed, including recurrence scaling, both positive coefficient expansions, and the conditional divisibility contradiction. No Lean or graph claim follows from that audit.
