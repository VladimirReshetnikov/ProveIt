# Independent audit of the relaxed/compacted comparison

Audited `comparison-supplement.md` on 2 October 2026.

**Verdict: approved as an algebraic consequence of the two forward expansions, with its stated separation between smooth-model and discrete conclusions.**

The logarithmic coefficient differences are exactly

    271/216 - 44/27 = -3/8,
    393/1120 - 141/140 = -21/32.

The n^(-1/3) terms and the z^3 terms cancel. Exponentiating leaves the displayed n^(-2/3) and n^(-1) terms unchanged, since the first nonlinear contribution is of order n^(-4/3). Thus both ratio expansions are correct, including the sign of the first surviving correction.

For the two smooth-model inverses, their logarithmic difference at n_r is

    log(gamma_c/gamma_r) - (1/4)log n_r + O(n_r^(-2/3)).

The inverse displacement is O(1). On that bounded interval the compacted derivative is `log(4n_r)+O(n_r^(-2/3))`; its curvature contributes only O(1/n_r). Dividing the difference by the derivative yields the stated remainder `O(n_r^(-2/3)/log n_r)`. The main term tends to 1/4. This does not imply convergence of the rounded integer threshold gap, and the supplement correctly says so.

Finally, c_n<=r_n gives N_r(Y)<=N_c(Y). The established Theta estimates alone give

    c_(n+1)/r_n >= const * n^(3/4)

for large n, hence c_(n+1)>r_n eventually. Taking n=N_r(Y) therefore proves the upper threshold bound N_c(Y)<=N_r(Y)+1 for sufficiently large Y. The claim that this coarser discrete result predates the proposed amplitude theorem is correct.

No additional proof change is needed.
