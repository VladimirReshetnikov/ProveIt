# A290268: number of terms in the expanded n-th derivative of x^(x^2)

[A290268](https://oeis.org/A290268) counts the terms of the fully expanded
n-th derivative of `x^(x^2)`. The entry conjectures (Reshetnikov 2017; restated
by Luschny 2017) that the sequence has generating function

```text
(1 + x + 2x^2 + 2x^3 + 2x^4 + 2x^5 + 2x^6 + x^7 + 2x^8 + x^9)
/ ((1 - x)(1 - x^2)(1 - x^8)),
```

equivalently that `a` satisfies the order-12 linear recurrence with signature
`{0, 2, 0, -1, 0, 0, 0, 1, 0, -2, 0, 1}`, equivalently the closed form

```text
a(2m)     = 2m^2 + 2m + 1,
a(2m - 1) = 2m^2 - floor(m/4).
```

This directory retains the investigation notes and the exact Python generators
behind the Lean development, now in
`Combinatorics/DerivativeExpansions/A290268/Lean/`.

## The exact model

Every derivative of `x^(x^2)` is an integer combination of the functions
`x^(x^2+j) * log(x)^k`. Writing

```text
(d/dx)^n x^(x^2) = sum_{j,k} c_n(j,k) * x^(x^2+j) * log(x)^k,
```

differentiating term-by-term gives the exact lattice recurrence

```text
c_0(j,k)     = [j = 0][k = 0],
c_{n+1}(j,k) = 2 c_n(j-1,k-1) + c_n(j-1,k) + (j+1) c_n(j+1,k) + (k+1) c_n(j+1,k+1),
```

and `a(n) = #{(j,k) : c_n(j,k) != 0}`. The support of `c_n` lies in
`{|j| <= n, j == n (mod 2), 0 <= k <= (n+j)/2}`. The recurrence reproduces the
worked example in the OEIS entry and the published data (`a(0..53)` checked,
and the closed form above checked against the model through `n = 66`).

## Generating-function reduction

Taylor expansion `sum_n z^n/n! (d/dx)^n x^(x^2) = (x+z)^((x+z)^2)` gives, for
`Q_n := x^(-x^2) (d/dx)^n x^(x^2)` viewed as a polynomial in `x^{±1}` and
`t = log x`:

```text
sum_n Q_n z^n / n! = exp((2xz + z^2) t) * (1 + z/x)^((x+z)^2).
```

Setting `w = z/x`, one finds `(1+z/x)^((x+z)^2) = exp(x^2 * phi(w))` with

```text
phi(w) = (1+w)^2 log(1+w) = w + (3/2)w^2 + sum_{m>=3} 2(-1)^(m+1) w^m / ((m-2)(m-1)m).
```

Both `x z t` (from the first factor, per power of `t`) and every monomial of
`x^2 phi(z/x)` carry equal weight 1 for the *depth* statistic
`D := (n+j)/2 - k`, which yields the key exact reduction

```text
c_n(j,k) = n! / (k! D!) * gamma(k, D, M),      D = (n+j)/2 - k,  M = n - k,
gamma(k,D,M) := [w^M] (2+w)^k * phi(w)^D.
```

(Verified exactly for all 3200 support-window points with `n <= 40`,
`k <= 9`, `D <= 9`.)

## Support characterization (conjectural, verified through n = 66)

The zero set of `gamma` on the lattice `k >= 0`, `D >= 0`, `M >= D` appears to
be exactly:

* `D = 0` and `M > k` (degree bound: `phi^0 (2+w)^k` has degree `k`), and
* the **hole line** `M = k + 4D + 1` with `k + D` even, `D >= 1`.

Translated back, `supp(c_n)` is:

* columns `j >= 0`: all `0 <= k <= (n+j)/2` (all coefficients positive);
* columns `j = -r < 0`: all `0 <= k <= (n-r)/2 - 1` **except** the single hole
  `k = (n - 2r + 1)/2`, present exactly when `r >= 3` and `n == r (mod 4)`.

Counting this set reproduces the conjectured closed form exactly: columns
`j >= 0` give `sum` of full ranges, negative columns give the `2m^2` totals,
and the holes account for the `floor(m/4)` correction (`floor((n+1)/8)` in the
OEIS form), whose period-8 behaviour is now explained by the congruence
`n == r (mod 4)` along `r = 3, 5, 7, ...`.

## The hole theorem (proved)

The exact vanishing on the hole line is a parity symmetry. Substituting
`w = e^u - 1` (so `log(1+w) = u`, `phi = u e^{2u}`) converts coefficient
extraction to a residue: with `B(u) := u/(e^u - 1)`,

```text
gamma(k,D,M) = [u^M] Ghat(u),   Ghat := (1+e^u)^k * u^D * e^{(2D+1)u} * B(u)^{M+1}.
```

Under `u -> -u`: `(1+e^{-u})^k = e^{-ku}(1+e^u)^k`, `B(-u) = e^u B(u)`, so

```text
Ghat(-u) = (-1)^D * e^{(M - k - 4D - 1)u} * Ghat(u).
```

On the line `M = k + 4D + 1` the exponential factor disappears, `Ghat` has pure
parity `(-1)^D`, and `[u^M] Ghat = 0` whenever `M - D` is odd, i.e. whenever
`k + D` is even. This is exactly the observed hole condition, including the
period-4 congruence. The change-of-variables lemma needed for `[u^M]` reduces,
for monomials `w^L`, to the classical residue identity
`[u^s](e^u (u/(e^u-1))^{s+1}) = 0` for `s >= 1`, which follows from
`s e^u/(e^u-1)^{s+1} = -d/du (e^u-1)^{-s}` — all provable in formal power
series over ℚ, no analysis required.

## Nonvanishing: solved strata and the open core

The remaining content of the conjecture is that `gamma(k,D,M) != 0` everywhere
else in the region `D >= 1`, `M >= D`. Status by stratum:

1. **Depth `D = 1` — solved.** Beta-integral representation (proved by
   induction on `k` from the coefficient recurrence, base case
   `phi_m = 2(-1)^(m+1)/((m-2)(m-1)m)`):

   ```text
   gamma(k,1,M) = (-1)^(M+1) * I(M-k-3, k),
   I(p,k) := ∫_0^1 t^p (2t-1)^k (1-t)^2 dt.
   ```

   For even `k` the integrand is nonnegative, so `I > 0`. For odd `k`, the
   reflection `t -> 1-t` symmetrizes the integrand to
   `(2t-1)^k · t^2(1-t)^2 · (t^(p-2) - (1-t)^(p-2))` (for `p >= 2`), which is
   pointwise `>= 0` and not a.e. zero unless `p = 2`, where it vanishes
   identically — exactly the hole `M = k + 5`. For `p < 2` the same
   factorization gives `I < 0`. Bulk `1 <= M <= k+2` follows by a small
   induction via `gamma(k+1,1,M) = 2 gamma(k,1,M) + gamma(k,1,M-1)` anchored
   at the (always positive) `r = 1` column `M = k+3`. Hence for `M >= 1`,
   `gamma(k,1,M) = 0` iff `k` odd and `M = k+5`.

2. **Depth `D = 2` — solved (paper proof).** The two-variable Beta
   representation gives, for `q := M - k - 5 >= 0`,

   ```text
   gamma(k,2,M) = c_M * ∫_0^1 ∫_0^1 (F(x) - F(y))/(x - y) dx dy,
   F(x) := x^q (2x-1)^k (1-x)^4,
   ```

   and integrating the divided difference against the exact Peano kernel of
   the double integral — computable in closed form as the entropy density
   `K(u) = -2(u ln u + (1-u) ln(1-u))`, since `K(u) = ∫_0^1 f_t(u) dt` over
   trapezoidal densities — one integration by parts yields
   `gamma(k,2,M) = ±∫_0^1 F(u) · 2 ln(u/(1-u)) du` (boundary terms vanish as
   `K(0) = K(1) = 0`). The weight `ln(u/(1-u))` is antisymmetric and positive
   on `(1/2, 1)`; antisymmetrizing `F` gives the pointwise sign-definite
   integrand `(2u-1)^k [u^q(1-u)^4 - (-1)^k u^4(1-u)^q] · ln(u/(1-u))`,
   nonzero unless `q = 4` with `k` even — exactly the `D = 2` holes.

3. **`k = 0` bulk — trivial** in the falling-factorial picture:
   `gamma(0,D,M)·M! = P_M^(D)(2D+1)` with `P_M(x) = (x-1)...(x-M)`
   (equivalently the Nørlund value `B_{M-D}^{(M+1)}(2D+1)·M!/(M-D)!`), and for
   `M <= 2D` the evaluation point lies beyond all roots, so every term of the
   derivative sum is positive.

4. **Open core: `D >= 3` negative region** (and general-`k` bulk). Here
   `gamma(0,D,M)·M!/D! = (-1)^q (2D)! q! · e_{D-1}(1, 1/2, ..., 1/(2D), -1,
   -1/2, ..., -1/q)`, `q = M-2D-1`, an elementary-symmetric-function value on
   a signed harmonic multiset; equivalently the coefficient of `t^(D-1)` in
   the real-rooted polynomial `(t+1)...(t+2D)(t-1)...(t-q)`. The `D`-fold
   Peano kernel argument breaks down for `D >= 3` because the symmetrized
   integrand is no longer sign-definite (the kernel's higher derivatives
   oscillate). Checked and ruled out empirically: clean 2-adic/3-adic
   valuation formulas; uniform tail sign-alternation induction (sign
   "wobbles" — e.g. `k=2, D=5` — never pass through zero but break
   alternation); all-terms-one-sign pairings.

**Literature status** (searched July 2026): the conjecture is open; no
published attack on A290268/A293239/A281434 exists. The closest proven result
is Štampach (J. Approx. Theory 262 (2021), arXiv:2011.13808): sign-alternation
and nonvanishing of `B_n^{(n)}(x)` at integers — the order-excess-0 analog of
what is needed here (order excess `D+1`). The hole direction is classical:
Nørlund's reflection `B_n^{(a)}(a-x) = (-1)^n B_n^{(a)}(x)`. Cautionary fact:
in the `x^x` family (A008296/A293239) the analogous coefficient array has a
*sporadic* zero at `A008296(8,5) = 0` beyond the symmetry-forced ones, so
nonvanishing genuinely needs proof, not just symmetry bookkeeping. For the
present `x^(x^2)` family, an exact scan found **no** unexpected zeros in
`k <= 20`, `D <= 14`, `M <= 400` (and none for `k <= 9, D <= 9, M <= 140`
from the earlier scan).

The Lean development therefore (i) proves everything except `D >= 3`
nonvanishing unconditionally where feasible (holes, `D = 1`, structural
zeros, count combinatorics), (ii) states the remaining nonvanishing as an
explicit hypothesis, and (iii) verifies the conjecture exactly on the
published OEIS range by verified computation.

## Lean formalization

The Lean library lives at
`Combinatorics/DerivativeExpansions/A290268/Lean/` (lean_lib `A290268`) and is
organized as:

| Module | Content | Status |
| --- | --- | --- |
| `A290268.Core` | The coefficient lattice `coeff n j k`, the term count `a n`, the closed form `closedForm n`, and the structural zero lemmas (parity, triangle `|j| ≤ n`, log-degree `2k ≤ n+j`). | unconditional |
| `A290268.ClosedForm` | `closedForm` satisfies the OEIS order-12 linear recurrence and the generating-function recurrence, and equals the piecewise quadratic form; the several conjectured shapes are interchangeable. | unconditional |
| `A290268.Count` | The conjectured support set `S n ⊆ ℤ × ℤ` and `card_S : (S n).card = closedForm n` (pure finite combinatorics; the hole count equals `⌊(n+1)/8⌋`). | unconditional |
| `A290268.Structural` | `coeff_negtop_eq_zero` (negative columns vanish at the triangle top) and `mem_S_of_coeff_ne_zero`: the structural inclusion `support ⊆ S n`, modulo a single hole-line hypothesis. | unconditional (mod hole) |
| `A290268.Hole` | `hole_vanishing`: the coefficient of `w^(k+4D+1)` in `(2+w)^k φ^D` is `0` when `k+D` is even (the `e^u−1` parity). | **not in the repository** (planned, never committed; see note below) |
| `A290268.DepthOne` | The complete `D = 1` stratum: `gam1 k M = 0` (for `M ≥ 1`) iff `M = k+5` with `k` odd, via the Beta integral and `t ↦ 1−t`. | **not in the repository** (planned, never committed) |
| `A290268.Series` | The reduction `coeff n j k = n!/(k!D!)·gam(k,D,M)`; discharges the hole hypothesis so `support ⊆ S n` becomes unconditional. | **not in the repository** (planned, never committed) |
| `A290268.Table` | Memoized table equal to `coeff`; `native_decide` verifies `a n = closedForm n` for every published term `n ≤ 53`. | unconditional |
| `A290268.Main` | `a_eq_closedForm_of_support`: the conjecture `a n = closedForm n` follows from `support = S n`, isolating the open content into the single nonvanishing inclusion `(j,k) ∈ S n → coeff n j k ≠ 0`. | unconditional reduction |

The upshot: `a n = closedForm n` (equivalently, the OEIS linear recurrence /
generating function, via `A290268.ClosedForm`) is proved *unconditionally for
all `n ≤ 53`* and, for general `n`, reduced to the single nonvanishing
statement — with the two solved strata (`D = 1`, holes) and the structural
inclusion already discharged.

*Correction (29 September 2026).* The modules `A290268.Hole`,
`A290268.DepthOne` and `A290268.Series` in the table above were never
committed; git history has no such files. The tracked development is
[`Combinatorics/DerivativeExpansions/A290268/Lean/`](../../Combinatorics/DerivativeExpansions/A290268/Lean/)
(`Core`, `ClosedForm`, `Count`, `Structural`, `Table`, `Main`), in which the
structural inclusion is conditional on the hole-line hypothesis and the
`D = 1` stratum and hole vanishing are not formalized. On paper, the
research-report collection's
[`power-tower-derivative-term-counts`](../../SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/power-tower-derivative-term-counts/README.md)
proves the depth-1 and depth-2 strata and bulk positivity, and its batch-42
addition closes logarithmic deficits 3 and 4 for every `n`; none of that is
formalized.

## Contents

* `computations/python/explore_support.py` — lattice model, OEIS/closed-form
  comparison, support-shape and anomaly tables.
* `computations/python/gamma_reduction.py` — exact verification of the
  `c_n(j,k) = n!/(k!D!) gamma(k,D,M)` reduction, the zero-set scan, sign
  tables, and bulk-positivity scan.
* `computations/python/valuations.py` — `D = 1` numerator interpolation and
  p-adic valuation scans (negative results retained deliberately).
