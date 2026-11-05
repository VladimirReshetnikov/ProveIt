# The missing first-index relation for the 72 reverse direction

The checked 72 graph and one-way map do not currently supply the first-index
congruence used by the existing 76Y/64 proof. Even **assuming** the auxiliary
half-index argument has established that the main Pell index `m` equals the
rank `R`, the free carrier yields a different congruence; it does not visibly
relate the first Pell index `n` to `R`. This is an analysis of the missing
proof step, not a proof of nonexistence, a compact44 counterexample, or a
new Lean theorem.

## Exact distinction

Use `Y=q³s`, `U=Y²`, `X=wq`, `a=(X+1)Y`, `H=4a+3`,
`D=a²+H`, and let the positive main root satisfy `g²=1+D c²`. The
[checked generic carrier bridge](../p64-qcube72-model-carrier-draft/README.md)
and [ring shape](../p64-qcube72-model-carrier-draft/FreeMainGraphShape.lean)
support extracting the scaled-square and carrier equations, once the
still-unchecked graph client is completed. Separately, identify the main
Pell index `m` using [`ArithmeticPellClassification.solution_index`](../../Lean/DiophantineConsistency/ArithmeticPellClassification.lean),
which requires the stated main Pell equation. With that additional
classification step, assume

```
U g = U(X+a c)+H h,       c=ycoord m a,       g=xcoord m a.
```

The checked carrier and ring-shape modules alone do not establish the Pell
index or this complete graph-level extraction.

If `m=R`, the existing
[Pell projection](../../Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean)
gives `g=2^R+a c+H z` for a natural `z`. Hence the free carrier gives

```
H | U(2^R−X)                  (integer divisibility).
```

Write `e=gcd(U,H)`, `U=e u`, `H=e v`. The
[P64 gcd lemma](../../Lean/DiophantineConsistency/Compact44/P64Early.lean)
shows `e | 9`; cancellation gives `v | 2^R−X`. If
`d=(2^R−X)/v` is the signed integer quotient, the same identity gives
`h=U z+u d`. The first norm separately gives
`k=2 ycoord n (2(XU−1)+1)` and `k≡2n (mod U)`. Thus the direct old
carrier would additionally require

```
u d + 2n − R − 1 ≡ 0 (mod U).
```

For example, if `e=1`, the free carrier makes `U | h`, but the remaining
condition is still `2n≡R+1 (mod U)`. The free carrier identity displayed above
contains no occurrence of that first index. This observation identifies a
missing link; it does not prove that the other graph constraints cannot
supply it.

The original [P64Early.early](../../Lean/DiophantineConsistency/Compact44/P64Early.lean)
uses the old carrier involving `gamma` to derive an early congruence
`(2n) % μ=R+1` with `R+1<μ`. The
[index comparison](../../Lean/DiophantineConsistency/Compact44/P72Exact.lean)
then uses it, the norms and size bounds to derive `m=R` **and** `2n=R+1`.
The [power recovery](../../Lean/DiophantineConsistency/Compact44/P72Power.lean)
uses this exact first/main relation to bound `2^R` and conclude `X=2^R`.
Replacing only `m=R` does not match those hypotheses.

For a compact44 72 zero, the transport and actual port inequalities support
the same rank bound `R+1<q⁴` as the old proof. The main Pell bound
`c≥2(a+2)`, combined with `X≥q`, `Y≥q³`, implies `c>2q⁴>2R`, without
using the missing early congruence. The signed half-index theorem would then
give `m=R` **if** its further large-`c` hypothesis
`(a+2)D²<c` and its other stated hypotheses were established. This packet
does not claim that all such hypotheses have been extracted from a 72 zero,
or that the large-`c` bound always holds.

## Narrow finite screen

[`screen.py`](screen.py) is an exhaustive bounded screen of a small,
**non-compact44** family: `beta=2`, `J=1`, `q=3`, `F=alpha=1`,
`R∈{43,47}`, `1≤s≤30`, and first Pell index `1≤n≤R`. These ranks come
from positive-transport inputs with `MC<beta` and `MF<2 beta`; K0 is allowed
0 or 1 to match the parity of any positive `w`. The screen includes an
occasional transport-invalid boundary point, so its searched domain is a
superset of that family.

For each `Y=27s`, any main-root candidate with `m=R` and positive carrier
must have `H | U(2^R−X)`. Since `H=4Y(X+1)+3`, this implies
`H | U(4Y(2^R+1)+3)`. The checker factors the latter finite integer,
verifies all factors with deterministic 64-bit primality checks, enumerates
its divisors as possible `H`, then checks the exact carrier and first/main
scale inequality `Yk<c<(Y+1)k`. It found two carrier-projection candidates
and no first/main scale match in the stated domain. Failure or timeout of a
factorization makes the checker fail, not skip a case. This small negative
screen does not bear on general or compact44 existence. Its retained output
is [`screen-result.json`](screen-result.json); run with
`python3 -I -S -B screen.py` (requires `/usr/bin/factor`).
