# Independent free-f² symbolic full-zero review

The [free-f² construction](../../research/p64-free-fsquare75-symbolic-full-zero/README.md)
checks out within its stated external scope. The 75-gate graph obtained by
replacing `f*f` with an independent positive `F2` has the specified full
positive zero, and `F2` is not a square. This defeats the direct pointwise
inverse but does not establish that the old graph has no other witness at the
same ports, decide existence equivalence or fixed compact44 ports, or prove an
iPRA theorem. No Lean or enormous witness coordinate was evaluated.

[`check_graph.py`](check_graph.py) independently pins the 76Y graph, verifies
that `f` occurs only in the `f2=f*f` row and that `f2` feeds exactly the two
stated rows, constructs the 75-gate rewrite, and verifies topological order
and liveness. It evaluates the original and rewritten graphs on 200
independent finite tuples under `F2=f²`; every residual and full output
matches. Universally this follows directly from the sole-use fact and the
forward substitution, whose positivity is immediate for `f>0`. The specified
small witness core yields `q=3,Y=27,U=729,X=6,a=189,H=759,D=36480,R=m`,
and `Lt=0`.

[`check.py`](check.py) independently computes outward 384-bit pair intervals
and proves `27k<c<28k`, without expanding Pell coordinates. Independent
matrix powers verify `(g,c)≡(488,538) (mod 759)`, main difference 506,
`A≡486` and `k≡428 (mod 729)`. Since `m≡184 (mod 729)`, gamma is integral.
It is positive because `k≥2j>m` and `g>(n−1)c>X+ac`; the ratio gives positive
`eta,zeta`. The Pell norms give `A0=1`, `g²=D c²+1`, and with `R=m` the
main carrier is `Ug`, so `M=0`. The same checker computes `c≡29 (mod 31)`
and `F2≡13`; direct enumeration of all squares mod 31 excludes 13, proving
`F2` nonsquare without relying on Euler's criterion.

The remaining symbolic construction is exact: `I=D c²`,
`F2−1=D c⁴`, so `W=I²−D(F2−1)=0`. The odd auxiliary Pell exponent makes
`x=T_m(I)` divisible by `I`; with `V=x/I`, the auxiliary norm yields
`Na=1`. Modulo `F2`, `I²≡1−n²`; the odd Chebyshev recurrence gives
`V≡−U_(m−1)(n)=−c` because `m≡3 (mod 4)`. Thus `(c+V)/F2=Q` is a positive
integer. The constant term of `T_m(X)/X` gives `V≡−m (mod c)`, while
`F2≡1 (mod c)`, hence `(m+Q)/c=T` is a positive integer and the graph's
`F2(cT−R)−c` is precisely `V`. This binds all residuals and establishes the
symbolic full zero. The finite recurrence controls in `check.py` are sanity
checks; the universal identities are the mathematical argument just stated.

The author bounded-check result was reproduced byte-for-byte. Exact author
source hashes are pinned in [`result.json`](result.json); independent graph
results are in [`graph-result.json`](graph-result.json). Run each script with
`python3 -I -S -B`.
