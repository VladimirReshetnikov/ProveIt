# Independent directed-log audit of the compact partial family

A separate directed-rounding calculation excludes a main-norm solution **within the pinned symbolic first-Pell family**, for every eta and gamma allowed by that construction. It does not exclude other zeros of the nine-variable graph, prove a parent bridge, or establish a Lean/iPRA consistency theorem. The independent calculation reconstructs the fixed compact integers, derives a different and tighter analytic envelope, and checks that its closed outward approximation contains no integer. It uses the **same MPFR 4.1.0 library**, so it is not independent verification of MPFR's transcendental implementation or directed-rounding guarantees.

The author's separate [directed-log packet](../ordinary9-compact-partial-directed-log-bound/README.md) has its pinned receipt reproduced. Its inequalities, signs and lower/upper denominator choices agree with source inspection; we found no concrete mathematical mismatch. Its wider envelope is `(n log(2Af)−2)/log(2A) < m < (n log(2Af)+5)/log(2A)`. This packet independently uses constants −1 and +3, without assuming equality of the main Pell index and graph rank.

## Separate elementary envelope

Use `X=q*w≥1`, `Y=q³≥8`, `M=X*Y²`, `Af=2M+1`, `A=Y*(X+1)+2`, and the exact first index `n`. The fixed-source reconstruction verifies `n<Af` and `2n<A`. At a putative main zero, standard Pell classification gives an m≥1 with `c=y_m(A)`; the first ordinate is `k=2*y_n(Af)` and `Yk≤c<(Y+1)k`. The separately pinned index argument gives `m<2n`.

For a multiplier T≥2, the standard recurrence gives `(2T−1)^(j−1)≤y_j(T)≤(2T)^(j−1)`. For `n<Af`, Bernoulli's inequality gives

```text
(2Af)^(n−1) < k ≤ 2*(2Af)^(n−1).
```

For `m<2n<A`, the same inequality gives

```text
(2A)^(m−1)/2 < c ≤ (2A)^(m−1).
```

Write `Lf=log(2Af)` and `L=log(2A)`. The lower bound on c and upper bound on its main Pell ordinate give

```text
m*L > n*Lf + log(A*Y/Af) > n*Lf−1,
```

because `2*A*Y>Af` and `log 2<1`. The other two bounds give

```text
m*L < n*Lf + log(4*(Y+1)*A/Af) < n*Lf+3.
```

Indeed `A≤3XY`, `Af≥2XY²`, and `Y≥8`, so the logarithm's positive argument is at most `6*(1+1/Y)<8<exp(3)`. Thus the strict envelope checked here is

```text
(n*Lf−1)/L < m < (n*Lf+3)/L.
```

These inequalities are mathematical arguments about standard integers and real logarithms. The source's Pell classification and the earlier first-norm family's validity are inputs; they are not newly Lean-checked here.

## Computational cross-check and limits

The checker reconstructs K′ from the pinned 943 coefficient rows and 41 slots by exact binary sums and cross-checks it against the earlier independent source checker. It separately reconstructs both masks from the pinned digit definitions and builds the rank using ordinary exact integer arithmetic. It checks the actual index size and the two multiplier inequalities above. No Pell coordinate is expanded.

MPFR evaluates both endpoint logarithms at `bitlength(n)+144 = 2,360,419` bits. Each endpoint begins with an outward-rounded integer-to-MPFR conversion, then uses outward log and arithmetic operations; positive numerator and denominator are checked, and the lower division uses the upper denominator while the upper division uses the lower denominator. The exact index n fits at this precision. A separate bound `upper<2n+2` ensures that both floor and ceiling values fit exactly. The recorded comparison is `ceil(lower)>floor(upper)`, so even the outward **closed** interval is integer-free. The calculation assumes correct MPFR directed-rounding semantics and the pinned source recipes; it is not a proof-object check.

The process applies a 768 MiB address-space cap, a 40-second CPU limit and zero core-file limit. A 55-second wall-clock timeout is supplied below; no gigantic Pell coordinates or large numeral outputs are produced. A failed assertion or exceeded guard gives no exclusion.

```sh
timeout 55s python3 -I -S -B research/ordinary9-compact-partial-log-interval-independent/check.py | cmp - research/ordinary9-compact-partial-log-interval-independent/receipt.json
```

No Lean, graph build, model/provider authentication or axiom audit was run.
