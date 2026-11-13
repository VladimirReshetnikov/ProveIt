# Independent review: fixed-mask modular families

**PASS, for the stated external integer claim.** We inspected the generated Lean
72-operation graph and the compact fixed-beta, low-mask and high-mask digit
sources. With the two K values `beta` and `2*beta` and the assignments in the
[construction](../../research/p64-qcube72-fixed-mask-all-moduli-controls/README.md),
the following argument applies for each positive integer N.

Let `q=beta*J+1`, `J∈{1,2}`, `Y=q³N`, `X=q`, `k=N+1`,
`U=Y²`, `P=XY²`, `ell=Pk`, and `c=kY+N`. Then `N|Y,c`, and
`N²|U,P,ell`. The actual graph gives `A0−1=−ell(ell+k)`,
`Dstar=U(X+ac)+H*N`, and `M=Dstar²−U²(1+Delta*c²)`; hence
`N²` divides both `A0−1` and `M`. With `f=i=y=1`, its strong and
auxiliary residuals simplify exactly to `W=c⁴` and `Na=1`, independent of
its rank expression. With `F=z=w=1`, `alpha=q−2` and `K=q−1`, the
transport residual `Lt=(K+w)(q−F−alpha)−F−z(q−1)` is zero.
Thus each summand of `(A0*Na−1)²+M²+W²+Lt²` is divisible by `N⁴`.
Since beta is positive, `q≥3`, and `ell,k>0`, the first squared summand
is strictly positive. This also covers `N=1`.

The exact mask definitions agree with the construction: beta is
`2^(67*8807)−1`; the low mask is the documented finite defect sum and
the high mask uses the listed 8807 little-endian base-`2^67` digits. The
independent control constructs these integers themselves, verifies both mask
bounds, compares every Lean graph operation against the JSON graph, and
evaluates the graph independently against the closed residual formulas at
15 moduli (including 1 and values beyond 64), each at both K values. It
checks `beta mod 3=1`, so the J=1 and J=2 families have `q mod 3=2,0`.
The author's 126-case control also reran with exit 0, and its standard output
was byte-identical to its retained `result.json`.

Run `python3 -I -S -B check.py`; the independent exit-0 output is
[result.json](result.json). Finite controls do not establish the universal
claim; the algebra above does. Neither the argument nor the controls give an
integer zero, an actual graph zero, an existential reverse implication, or
any conclusion about compatible p-adic limits, unbounded precision or extra
hypotheses. No Lean theorem was checked in this review.

Reviewed construction SHA-256: README
`5050874f1073cf8b2d785707612468aa08dd0ee36865f48945607804d159e149`,
checker `4b702ade4a72fcd2c68c85a6015b7c53b61af1fec00744f3390bc2e20d4ba61e`,
retained result `6321ba6068b7852d020cd68dd4024829943819e7d1f033e7b3251291163937f6`.
Independent checker SHA-256
`4e02e7f8fb00277daedaa65570a2dd4fafdeed0b5b605b24c1a2de148903fa35`,
independent result `790e98010f6fc94975a9b09043d80d8b8701b7ddf7705d528f60edeb8fdf21d9`.
