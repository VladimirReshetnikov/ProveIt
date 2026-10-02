# Inverse asymptotics: independent audit

**Verdict.** The proposed Lambert-W inversion is correct, including the absolute error `o(1/log n0)` for the inverse of the actual log-linearly interpolated counts. Integer thresholds require a separate rounding statement. The optional all-orders relaxed inversion is valid, but a pure smooth inverse expansion must not be identified with the log-linear inverse beyond the interpolation error of order `1/(n log n)`.

This audit assumes the supplied counting equivalents. It does not independently prove their amplitudes or the relaxed all-orders expansion, and it does not infer a DFA all-orders theorem.

## Insertable report section

Let `T_n` denote either `R_n` or `B_n`, and put

`(A,C)=(27/4,C_R)` or `(27/2,C_B)`, respectively,

`c=3·3^(1/3)a_1<0`, `L=log y`,

`w=W_0(sqrt(A)L/(2e))`, `n0=L/(2w)`, `D=2(w+1)`.

Here `W_0` is the principal real Lambert-W branch. Let `x(y)` be the inverse obtained by linearly interpolating `log T_n` between consecutive integers. As `y→∞`,

`x(y)=n0−[c n0^(1/3)+(8/3)log n0+log(2πC)]/D+o(1/log n0)`.

Equivalently,

`x(y)=n0−c n0^(1/3)/D−4/3−[log(2πC)−(4/3)log A]/D+o(1/log n0)`.

In particular, `x(y)~n0~L/(2log L)`. The stretched-exponential term raises the inverse by

`−c n0^(1/3)/D ~ [−c/2^(4/3)] L^(1/3)/(log L)^(4/3)`.

The least integer threshold `N(y)=min{n:T_n≥y}` satisfies exactly `N(y)=ceil x(y)` for all sufficiently large `y`, and hence satisfies the displayed inverse formula with `O(1)` in place of its final `o(1/log n0)` remainder. An asymptotic approximation must not itself be rounded and declared exact without excluding targets sufficiently close to an integer threshold.

## Proof of the stated precision

The leading equivalent and Stirling's formula give

`log T_n = H0(n)+g(n)+o(1)`,

where

`H0(t)=2t log t+(log A−2)t`,

`g(t)=c t^(1/3)+(8/3)log t+d`, `d=log(2πC)`.

The coefficient `8/3` consists of the given `5/3` and the `1` from the two factorials. The factorial constant is `2π`, not `sqrt(2π)`.

Since the remainder is `o(1)` on integers, consecutive differences are

`log T_(n+1)−log T_n = 2log n+log A+o(1)>0`

eventually. Thus the relevant inverse and least threshold are well defined in the tail, without needing a separate monotonicity assumption. Linear interpolation of the smooth function `H0+g` incurs `O(1/n)`, because its second derivative is `O(1/n)`. Interpolating the sequence of `o(1)` errors remains uniformly `o(1)` on the tail. Consequently the interpolated exact logarithm is

`H0(t)+g(t)+o(1)`

for real `t→∞` as well.

Writing `s=sqrt(A)/e`, the equation `H0(n0)=L` is `2n0 log(sn0)=L`. Its exact solution is the displayed Lambert-W expression, and

`H0'(n0)=2log n0+log A=2(w+1)=D`.

Set `δ=−g(n0)/D=O(n0^(1/3)/log n0)`. Taylor expansion gives

`H0(n0+δ)+g(n0+δ)−L`

`=O(δ²/n0)+O(n0^(−2/3)|δ|)+O(|δ|/n0)`

`=O(n0^(−1/3)/log n0)=o(1)`.

Adding the exact log-count's `o(1)` remainder leaves an `o(1)` residual at `n0+δ`. Every relevant slope of the actual log-linear interpolant is asymptotic to `2log n0`. Dividing this residual by the local slope proves

`x(y)−(n0+δ)=o(1/log n0)`.

Finally, `(8/3)log n0=(4/3)D−(4/3)log A`, proving the equivalent sharpened form with the universal continuous correction `−4/3`.

## Integer thresholds: exactly what is and is not established

For `N(y)=min{n:T_n≥y}` and the actual log-linear inverse, eventual strict monotonicity gives

`N(y)=ceil x(y)`, `0≤N(y)−x(y)<1`.

For the alternative convention `M(y)=max{n:T_n≤y}`, the corresponding exact relation is `M(y)=floor x(y)`. At `y=T_n`, both conventions give `n`.

If `xhat(y)` denotes the displayed asymptotic approximation, the valid result is `N(y)=ceil(xhat(y)+o(1/log n0))`, or more informatively `N(y)=xhat(y)+O(1)`. The formula `N(y)=ceil xhat(y)` is not uniformly justified: even an error tending to zero can cross an integer. It does hold along target sequences where the distance of `xhat(y)` from the integers exceeds a proved bound on its approximation error. A leading equivalent supplies no explicit numerical such bound.

## Optional relaxed all-orders inversion

Assume the separately audited relaxed result has, for every fixed `M`, the form

`R_n=C_R(n!)² A^n exp(c n^(1/3))n^(5/3) [1+Σ_(k=1)^M r_k n^(−k/3)+O(n^(−(M+1)/3))]`,

with `A=27/4`. Taking logarithms and including Stirling yields

`log R_n=H0(n)+c n^(1/3)+(8/3)log n+d+Σ_(k=1)^M ℓ_k n^(−k/3)+O(n^(−(M+1)/3))`.

For example, `ℓ_1=r_1`, `ℓ_2=r_2−r_1²/2`, and `ℓ_3=r_3−r_1r_2+r_1³/3+1/6`; the `1/6` is the first two-factorial Stirling correction. Every later `ℓ_k` is computable from the `r_k` and the Stirling series.

### A. A smooth formal inverse, or any specified smooth asymptotic extension

Write

`g_M(t)=c t^(1/3)+(8/3)log t+d+Σ_(k=1)^M ℓ_k t^(−k/3)`,

`H_M(t)=H0(t)+g_M(t)`.

The large real root `z_M` of `H_M(z_M)=L` is constructive to arbitrary precision. Start with `z^(0)=n0` and iterate

`z^(j+1)=z^(j)−[H_M(z^(j))−L]/H_M'(z^(j))`.

On the relevant neighborhood, `H_M'~2log n0` and `H_M''=O(1/n0)`. Therefore, if `e_j=z^(j)−z_M`,

`e_(j+1)=O(e_j²/(n0 log n0))`,

starting from `e_0=O(n0^(1/3)/log n0)`. In particular,

`e_j=O(n0^[1−(2/3)2^j]/(log n0)^[2^(j+1)−1])`.

Any requested algebraic accuracy is reached after finitely many iterations. Increasing `M` controls the omitted asymptotic terms. If a chosen smooth extension has the stated uniform log asymptotics, its inverse differs from `z_M` by `O(n0^(−(M+1)/3)/log n0)` (with `o` in place of `O` under the corresponding `o` convention).

An equivalent formal reversion rule is

`z=n0+Σ_(k≥1) [(-1)^k/k!] (d/dL)^(k−1) { g(n0)^k / D }`,

where `d/dL=D^(−1)d/dn0` and `g` is the full formal logarithmic correction. Interpret this as an asymptotic re-expansion, not a claim that the infinite series converges. For example, the second reversion term is

`g(n0)g'(n0)/D²−g(n0)²/[n0 D³]`.

This also independently checks the sign and scale of the first neglected smooth term in the leading inversion.

### B. The actual log-linearly interpolated inverse, to all orders

The all-orders statement above is initially a statement at integers. To retain the exact interpolation convention, define the piecewise-linear operator

`(I f)(t)=(1−θ)f(m)+θ f(m+1)`, `m=floor t`, `θ=t−m`.

Let `x_M` solve `(I H_M)(x_M)=L`. Interpolation preserves the uniform integer remainder, and the slopes are asymptotic to `2log n0`, so

`x(y)−x_M=O(n0^(−(M+1)/3)/log n0)`.

This is a rigorous, constructive all-orders inverse of the actual log-linear interpolation. It can be evaluated directly from the two adjacent values of `H_M` once the bracket is found. It avoids assuming any derivative bounds on the counting remainder.

The difference from a smooth model matters at sufficiently high order. Taylor expansion at `t` gives

`(I H_M)(t)−H_M(t)=Σ_(r≥2) H_M^(r)(t)/r! [(1−θ)(−θ)^r+θ(1−θ)^r]`

to any finite order, with the Taylor remainder. Its first term is

`θ(1−θ)H_M''(t)/2=θ(1−θ)/t+O(t^(−5/3))`.

Consequently, for the inverse of the smooth model and of its linear interpolation,

`x_M−z_M=−{z_M}(1−{z_M})/[z_M H_M'(z_M)]+O(z_M^(−5/3)/log z_M)`.

The fractional-part factor is continuous and Lipschitz across integer boundaries, so this estimate remains valid there. In particular the first interpolation correction is of order `1/(n log n)`, with a nonpositive sign: the leading log-count is convex, so its chords lie above it. A pure series whose coefficients depend only smoothly on `log n0` cannot silently absorb this lattice-dependent term.

## Diagnostic check

`check_inverse.py` and `numerical-checks.json` test the algebra in a synthetic exact model using `2log Γ(n+1)`, both values of `A`, `C=1.7`, and targets whose exact log-linear inverse is `10^p+0.37`. The error multiplied by `log n0` tends to zero; its ratio to the predicted leading smooth second-reversion term tends to one. These checks confirm implementation and signs but do not replace the proof or test the underlying enumeration theorem.
