# Independent mathematical audit of the A202058 fine addendum

Audit date: 2 October 2026. This audit does not modify the frozen report or the main addendum. The complete integrated TeX and the final edits were reviewed. The verdict below is tied to the exact source and PDF hashes recorded at the end.

## Final integrated verdict

The new weighted-residual/padding argument is sound. It proves a quadratic-logarithm **upper** coefficient bound. The improved broad-window lower bound and the asymmetric threshold inverse are also sound. They do not prove a matching logarithmic-square lower bound, a limiting logarithmic-square coefficient, a ratio limit, a multiplicative equivalent, or an all-orders expansion.

No substantive mathematical gap was found in the integrated theorem proofs. The preliminary research note omitted a domain qualification in one Chernoff statement; the integrated lemma correctly requires **q≥q₀** for an absolute threshold q₀, uniformly in N≥1 and 0<ε<1/2. Its application has q→∞. The formal and numerical material is clearly separated from proved statements.

## 1. Weighted residual, with independent sign checks

Let D=s+Ru, r=h(k)/D and λ=Db/R. The frozen kernel g is decreasing separately on the intervals cut by the integer breakpoints s and k. Every summand g(i) is a left endpoint of a unit interval within one such piece. Thus S≥λ, including intervals adjoining either jump. Its absolute quadrature-error bound yields 0≤S−λ≤3√2 exp(q/2).

The child rank denominators are D−1, D+R−1, D+1, D+1−R. For duplicate ascent only,

    r(i)−r_child = i(R−1)/[D(D+R−1)] ∈ [0,1/D].

All other child ranks are at least r(i); all four absolute differences are at most 4/D. Consequently

    exp(−4q/D) λ ≤ Tψ/ψ ≤ exp(q/D) S.

The time derivative is λ−bB, not λ+bB. Since |B|≤1, the correct upper residual is (Tψ−∂tψ)/(bψ), bounded by

    (D/R)(exp(q/D)−1) + 3√2 exp(q/2)exp(q/D)/b + 1.

The inequalities R≥1, exp(z)−1≤z exp(z), and

    exp(q/2)/b = q/[√R(1−exp(−q))] ≤ q+1

give exactly the stated upper estimate. The last inequality follows from exp(q)≥q+1, with the continuous q=0 value. In the opposite direction,

    (∂tψ−Tψ)/(bψ) ≤ (D/R)(1−exp(−4q/D))+1 ≤ 4q+1.

Integrating this last q-time residual gives E_−(q)=2q²+q with the stated sign. No absolute-error bound has been substituted for a one-sided bound incorrectly.

## 2. Padding and infinite-state comparison

Fix a horizon Q and a fixed integer L≥Q. For I_L(s,u,k)=(s+L,u,k+L), the original transition indexed i becomes exactly the padded transition indexed i+L, in all four cases. The L additional transitions have nonnegative contributions. Thus

    T(f∘I_L) ≤ (Tf)∘I_L

for nonnegative f. This is a one-sided inequality, not equality or a lower comparison. Padded states remain in the invariant state space and have D≥L+1. Therefore exp(q/D)≤e throughout 0≤q≤Q.

The displayed H satisfies

    H′(q)=e(1+3√2)q+3√2e+1,

which is precisely the simplified upper residual at exp(q/D)=e. Since L stays fixed during differentiation, exp(H)ψ(q,I_Lx) is a global supersolution with initial value one.

For completeness, the infinite-state upper comparison is legitimate: the jump chain with generator T−mI is nonexplosive because its rate after j jumps is at most m_initial+j. Stopping on m≤M gives a finite state space. The weighted supersolution inequality bounds the surviving terminal expectation; the nonnegative exit term may be discarded. Monotone convergence yields F≤G_+ without any bounded-operator assumption.

The lower comparison needs and receives additional control. For fixed physical time t choose δ>0 with t+δ<T and a single padding L valid up to t+δ. For physical v∈[0,t], the ratio of the unpadded subsolution at v to that later padded supersolution at v+δ is bounded by

    C exp(−[p(v+δ)−p(v)]s−[q(v+δ)−q(v)]u) ≤ C exp(−ηm).

The rank terms are uniformly bounded at the fixed horizon, L is fixed, and both positive parameter increments have positive minima on the compact interval. The exit occurs at m=M+1. The later supersolution bounds its weighted contribution by C exp(−η(M+1))G_+(t+δ,x), which vanishes. This proves the lower comparison for every state. There is no unproved comparison of an arbitrary subsolution with an unbounded operator.

Uniformity in x follows directly: the difference of padded and original log profiles is Lp−q(r_padded−r), bounded above by Lp+q. In fact r_padded≥r, so Lp already suffices. Choosing L=ceil(q) for each completed horizon gives an absolute O((q+1)²) error uniform over all states. One must not differentiate L=ceil(q) as a varying function; the argument fixes it at each horizon.

## 3. Coefficient upper bound

The exact root indexing is F(t,(1,1,1))=A′(t), where A(t)=Σa_n t^n/n!. Positivity gives A(t)≤1+tF(t,x_0) and a_n/n!≤A(t)t^(−n). At Q=2log(n+2), log F(t(Q),x_0)=O(Q²). The endpoint tail T−t(Q)=O((Q+2)exp(−Q/2)) implies n log(T/t(Q))=O(log(n+2)). Therefore

    log[a_n/(n!μ^n)] ≤ C(log(n+2))².

The inequality excludes positive exp(c n^σ) corrections with c,σ>0, even with fixed powers or logarithmic powers. It does not exclude negative stretched-exponential corrections.

## 4. Improved Chernoff bound and lower coefficient extraction

For x_N=(N,1,N), the profile is Np+qR/(N+R). The new barriers therefore give log F(t(q),x_N)=Np(q)+O((q+1)²), with constants independent of N.

For q sufficiently large, the frozen bounded-shift calculation applies unchanged. Writing d=(log t)′, M=p′/d and

    H_q(v)=p(q+v)−p(q)−M(q)(log t(q+v)−log t(q)),

one has H_q(0)=H_q′(0)=0, H_q″(v)→exp(−v/2)/4 uniformly on |v|≤1, and M(q)d(q+v)→exp(−v/2)/2. Hence |H_q(v)|≤v²/2 and the needed tilt increment is at least |v|/4. The choices v=±ε/8 yield −3Nε²/128. Errors from the two function evaluations are O((q+1)²), uniformly in N and ε.

Choose a sufficiently large fixed K, then

    N=ceil(K n^(2/3)(log n)^(2/3)), ε=2N/n,
    NM(q)=(1−4ε)n.

The target M(q)=n/N−8 tends to infinity. Since M is continuous and eventually strictly increasing, a solution exists on its increasing large-q branch. From M(q)∼T exp(q/2)/(√2 q),

    q=(2/3)log n+(2/3)log log n+O(1).

The O(1) constant may depend on fixed K. No uniformity over arbitrarily varying K is needed. Moreover Nε²=4N³/n²≥4K³(log n)². The function-error constant can be chosen independent of K, and q≤log n eventually for each fixed K. Thus K can first be chosen large enough to make the tail less than 1/2, and then n chosen sufficiently large. There is no circular parameter selection.

The central interval has endpoints exactly

    n−10N+16N²/n  and  n−6N−16N²/n.

It is therefore contained in [n−12N,n−N] for sufficiently large n. A central integer j with tilted mass at least F/(4εNM+6) exists. The root has a path of **N−1** steps to x_N, so the exact original-word index is **N+j**, not N+j+1 or N−1+j. Positivity gives a_(N+j)≥T^j1(x_N). The monotone extension injection then gives a_n≥T^j1(x_N), since N+j≤n.

Finally log(n!/j!)≤(n−j)log n≤12Nlog n. The q² and logarithmic pigeonhole losses are smaller. Dropping Np≥0 and using −j log t(q)≥−n log T proves

    log[a_n/(n!μ^n)] ≥ −C n^(2/3)(log n)^(5/3).

## 5. Threshold inverse and exact regularity identities

Let f(x)=x log(x/(eT)), x=y/W(y/(eT)), so f(x)=y. Stirling adds only O(log n) to the coefficient envelopes. At n=x−C log x, the decrement f(x)−f(n) has order C(log x)² and dominates the upper error for large fixed C. At n=x+C x^(2/3)(log x)^(2/3), the increment has order C x^(2/3)(log x)^(5/3) and dominates the lower error. Since f′(x)=log(x/T) and both displacements are o(x), these estimates are uniform on the bracketing intervals. Monotonicity of a_n and integer rounding prove the stated asymmetric bounds. Both signs and the powers of log are correct.

Direct child summation verifies

    Tm=m²+u−k,
    Ts=ms+m−2s,
    Tk=m(m+1)/2−s,
    T(m²)=m³+2m(m−s−k)+m−|s−k|.

Size-biasing by the child count m gives the displayed M_(n+1) identity. Normalized log-concavity at center n+1 is exactly

    (n+1)(Var_n(m)+E_n(u−k))≤M_n².

The claimed PF3 minor is −1/3, and the length-seven multiplicity polynomial has discriminant −84159. These disprove those stronger proposed routes; they do not disprove normalized log-concavity. If global normalized log-concavity were proved, its decreasing ratios and the known root limit would give a_n/(n!μ^n)≥1. This implication is valid but remains conditional.

## 6. Formal mechanism and theorem/conjecture separation

The exact frozen circle kernel and its Fourier/Poisson inverse were independently checked. The continuum first-order residual average simplifies to

    q I(q)+q(z−1)/(2R)+1/2,

including the rank-interface and wrap boundary terms. Its stated large-q expansion is correct. These are identities or expansions in the frozen continuum limit; they do not supply uniform estimates for the evolving discrete chain.

The proposed q²/6 scalar exponent, the consequent candidate (2/3)(log n)² coefficient scale, and any fitted power or amplitude must remain labeled formal/conjectural. The missing uniform rank/composition correction, weighted finite-state boundary/return control, and individual-coefficient transfer are genuine unresolved steps. In particular the original-profile root jump rate in q-time is O(q exp(−q/6)), so an ordinary fast-escape assertion is false. No such assertion is needed in the proved bounds.

## Reproducibility and scope

A fresh verifier, `verify_fine_independently.py`, independently implements the four transitions, integrates the piecewise frozen kernel, checks residuals and moment identities on finite grids, directly enumerates words through length ten, checks the finite coefficient inequalities, and symbolically simplifies the continuum average. Its JSON result is recorded separately. These are diagnostics supporting the analytic audit, not proofs of uniform statements or of asymptotic conjectures.

The final integrated TeX was reviewed in full, including its conditional inverse and explicitly defined transformed generator. This audit does not certify external literature novelty or formally verify the complete frozen foundation from first principles; it independently checks the cited transfer identities and the mathematical steps newly used here.

## 7. Final edits and integrated findings

The conditional inverse added after the main review is correct. If h_n∼(2/3)(log n)², then Stirling gives log a_n=f(n)+(2/3)(log n)²+o((log n)²). Evaluating at x−(2/3)log x±ε log x and using f′(x)∼log x brackets the threshold for every fixed ε>0. Thus N(y)=x−(2/3)log x+o(log x), conditional on that conjecture. No ratio limit or discrete differentiation assumption is needed for this bracketing argument. The report correctly labels the formula conditional.

The explicit transformed generator L^ψf=Σ_i[ψ(x_i)/ψ(x)](f(x_i)−f(x)) removes the earlier notational ambiguity about time scales. Dividing its rates by b gives q time. The displayed composition drift remains a formal large-state calculation and does not enter a theorem proof. The final bibliographic and build-timezone edits do not change the mathematics.

The integrated theorem statements, proof sections, abstract, conjecture label, numerical cautions, and closing list of missing estimates are mutually consistent. In particular, no theorem claims the coefficient 2/3, normalized log-concavity, a matching fine lower estimate, a limiting amplitude, or an all-orders inverse.

## 8. Reviewed source hashes and frozen-copy check

SHA-256 hashes identify the reviewed material. The TeX/PDF match the writer's announced final hashes. The complete hash manifest is `independent-audit-manifest.json`; it also records the independent diagnostic files and the hashes of every bundled frozen-foundation file.

- a202058-fine-addendum.tex
  SHA-256: 26b7cc53c612e6f4ddacef5e1bba9262b3f80da805625381467cd4f99012048a
- a202058-fine-addendum.pdf
  SHA-256: e42b6e042346c766551844517897f3d70aa322fd657f558b51dcdcd975580f1a
- support/fine-research/padded-barrier-proof.md
  SHA-256: 0c5fdcd5c5a991db44edd6e2020af0d269cb08c787ffe40b27b879e70866d7da
- support/fine-research/improved-coarse-lower.md
  SHA-256: 3d42810f3354dfc0cdb3cf74f5358b7b585e0d8da36136ae9e014cd663d2a58c
- support/fine-research/coefficient-obstruction.md
  SHA-256: 5a809bdb23f727daac1ead8804d2d8f37ccb746ec6c39f6965b748a7a9750487
- support/fine-research/kernel/audit-padded-barrier.md
  SHA-256: 50ab499965e882f12ecce1b03c473fb218d4e52f395e3c0731da6c2dae7e2013
- support/fine-research/kernel/formal-kernel-audit.md
  SHA-256: 016c34f64c38bfd9ed5a1b63c9c81d96ee1e0062c316c64ba66241189a2151a6
- support/fine-research/lognormal-route.md
  SHA-256: 8cd2827a220dfac24002c03ea9539c4240823a69795b73d39210b52ce26b2527
- dependencies/frozen-foundation/a202058-report.tex
  SHA-256: 8d7bb13a64982e1479996719882d9f188e00899108d4f27e44b42076e1687e1f
- dependencies/frozen-foundation/root-limit-proof.md
  SHA-256: 14c56e5d26ddc6e6204b782dfb93be231265a43782f1151f854164d7152b0e49

All 18 bundled frozen-foundation files were compared byte-for-byte by SHA-256 with their original counterparts; every comparison passed. The originals were only read.

The final PDF differs from the initially reviewed build only in the larger figure labels and adjusted plot margins on page 12, as reported by the integrator. The mathematical TeX hash is unchanged. The final PDF hash above supersedes the earlier build. The included figure, rendering source, and underlying diagnostic data are identified below.

- support/fine-research/numerics/correction-diagnostics.pdf
  SHA-256: 0e7c768ad6ab312dbaf6aa96cf1248202b468f9df2328cb179bcb0560ec0933f
- support/fine-research/numerics/correction-diagnostics.png
  SHA-256: cb3387afd0f038d24db108d645e9fc268589e07c39cff55808cc24c5564b1367
- support/fine-research/numerics/plot_diagnostics.py
  SHA-256: 6a0440a26c56db006a1888f8e8accc01d858a559b596e70802db8b33d0d60d3b
- support/fine-research/numerics/diagnostics.tsv
  SHA-256: 599cec85b0e2c05a0932c040d8ac5d7cf04491cd9f1f1705ef1f29ad0a858688
