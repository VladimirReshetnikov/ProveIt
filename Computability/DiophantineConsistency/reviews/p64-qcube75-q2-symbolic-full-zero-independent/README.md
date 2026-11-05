# Independent review: symbolic q²-scale full zero

The [proposed witness](../../research/p64-qcube75-q2-symbolic-full-zero/README.md)
checks out mathematically within its stated external scope. It is a full
positive zero for the modified 75-operation graph at the displayed natural
ports, with `Y=18` and `27∤18`. It obstructs the particular pointwise inverse
that keeps this `Y`; it does not disprove existential equivalence, address the
compact44 ports, or give a Lean/iPRA proof. No gigantic strong or auxiliary
coordinates were expanded, and no Lean ran in this review.

The companion [`check.py`](check.py) independently bounds the two Pell
coefficients by binary exponentiation of **pairs** with outward rounding,
using 384-bit mantissas. Unlike the source packet's square-root bounds, this
checks `18k<c<19k` directly without radicals or full Pell coordinates. A
second independent calculation uses matrix powers modulo 291 and 324 to
check `(g,c)=(131,88)`, `d=194`, `A=216`, and `k=188` in their respective
moduli. The Chebyshev finite controls are sanity checks only, not a proof of
the universal identity. Exact input pins and results appear in
[`result.json`](result.json). Run the checker with `python3 -I -S -B check.py`.

The interval arithmetic is rigorous because all entries and coefficients are
nonnegative; truncating a product's pair down or up preserves the two
componentwise bounds. The separately stored binary exponent is exact. In the
first and main norm, the bounds give `eta,zeta>0` and `c=18k+eta`; the Pell
norms yield `A0=1` and the prescribed main root. The exact integer `A` follows
from `g−X−ac ≡194 (mod 291)` and `gcd(324,291)=3`; dividing by 97 then
shows `A ≡216 (mod 324)`. Together with `k ≡188` and `m ≡79 (mod 324)`,
this makes `gamma` integral. It is positive because `A>0` and `k≥2j>m`.
The graph's `R=m`, `Lt=0` and aligned carrier `Dstar=U g` are direct
substitutions; the chosen ports and all listed small witnesses are nonnegative
or positive as required.

For the strong factor, the binomial coefficients show `c²|L` in
`(g+c√D)^c=f+L√D`; the norm gives `I²=D(f²−1)` with `I=DL=i c²`.
For auxiliary odd exponent `m`, `T_m(I)` is divisible by `I`, and the
quadratic norm proves `Na=1`. The key congruence is valid uniformly: define
`S_r(z)=T_(2r+1)(x)/x` with `z=x²`. Both `S_r(1−n²)` and
`(−1)^r U_(2r)(n)` have the same first two values and satisfy the same
second-order recurrence, so `V≡−U_(m−1)(n)=−c (mod f²)` when `m≡3 mod 4`.
Thus `Q=(c+V)/f²` is a positive integer. The constant term of
`T_m(x)/x` is `−m`, and `c²|I`, so `V≡−m (mod c)`; since `f²≡1 (mod c)`,
`T=(m+Q)/c` is also a positive integer. This binds the graph's actual
`f²(cT−R)−c` to `V`. Consequently all residuals `A0−1`, `Na−1`, `M`, `W`
and `Lt` vanish. The recurrence and norm reasoning is a mathematical source
review, not a new kernel check.
