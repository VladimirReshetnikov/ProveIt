# Final source review of the L-convex area report

Date: 1 October 2026.

Verdict: **approved for the mathematical claims checked below**, conditional on the cited, known area generating function. No substantive mathematical defect or formula drift was found. This is an internal mathematical review, not external peer review or machine-checked formal verification. It makes no independent claim of literature priority.

## Exact source versions

- Reviewed article: `article/lconvex-asymptotics.tex`
- Article SHA-256: `97170bff99f656f8e9af8ef0f909035eab4fb6fff9831610bb76e00f24f4fd0d`
- Baseline proof note SHA-256: `17b92af4f7d9f8472f3c7cf78f6e98d7d95131cb84bf70144e339fd5fe64ff56`
- Baseline independent audit SHA-256: `59aeb8c634722b96c50599027374186f4b165a381ac53a7a2f475df63ecdbbc3`

The earlier independent audit already checked the exact decomposition, Heine/Fine substitutions, global residual and minor-arc bounds, uniform local expansion, coefficient transfer, Bessel formula, correction coefficients, and logarithmic inverse coefficients. This review compared their integrated presentation against that exact audited revision rather than treating numerical agreement as proof.

## Additional and integrated claims checked

1. **Optimized exact-remainder coefficient bound.** The whole-circle estimate for R gives `|[q^n]R| <= O(t^(-1/2) exp(nt + pi^2/(2t)))`. Taking `t = pi/sqrt(2n)` proves `O(n^(1/4) exp(pi sqrt(2n)))`. Dividing by the proved leading equivalent yields the printed relative bound with factor `n^(7/4)` and exponential gap `pi(sqrt(13/6)-sqrt(2)) sqrt(n)`. The report correctly distinguishes this exact generating-function remainder from an optimally truncated algebraic expansion or a full transseries.

2. **Lambert-W branch and correction terms.** The leading equation gives `y_0 exp(-y_0/3) = (K/X)^(1/3)`, so its increasing large branch is exactly `-3 W_{-1}(-(K/X)^(1/3)/3)`. The displayed coefficients of `1/y_0`, `1/y_0^2`, and `1/y_0^3` cancel the logarithmic forward equation through cubic order. Independent symbolic substitution gives residual `O(y_0^(-4))`. The derivative of the leading logarithmic equation tends to one, so the stated inverse-error order is valid for the large inverse model. The manuscript explicitly avoids assigning a canonical noninteger inverse to the discrete sequence.

3. **Shrinking threshold brackets.** Since `a_n/F_M(n) = 1 + O(n^(-M/2))` and `(log F_M)'(x) ~ sqrt(kappa/x)`, the necessary index displacement is `O(x^(-(M-1)/2))`. Enlarging the fixed constant makes the comparisons strict on the two sides; applying ceilings gives the displayed lower and upper bounds without an off-by-one problem. For `M >= 2` the unrounded width tends to zero. The manuscript correctly states that its constants and starting threshold are not numerically certified and that targets close to actual integer thresholds require care. The row-enlargement injection and eventual strict increase are consistent with the earlier audit.

4. **Eventual strict log-concavity.** The review added Corollary 6.1. Taking `M=5`, the logarithm of the coefficient expansion is an explicit smooth finite expression plus `O(N^(-5/2))`. The second difference of the three remainder values remains `O(N^(-5/2))` by the triangle inequality; no unjustified differentiation of an asymptotic error is used. Direct differentiation/Taylor expansion of the explicit expression gives

   `log(a_n^2/(a_(n-1) a_(n+1))) = sqrt(kappa)/(2N^(3/2)) - 3/(2N^2) + O(N^(-5/2))`.

   Its leading term is positive, proving eventual strict log-concavity. No effective first index is asserted.

5. **Transcription and normalization.** The integrated exact products, sums, powers, coefficient algorithm, displayed coefficients, shift `N=n-1/6`, leading constant, and inverse polynomials match the audited note. The unshifted first correction is consistent with expanding the shift. The transformation proof now explicitly assumes `q != 0` and extends the identities to zero by continuity, matching the baseline audit's treatment.

## Presentation check and handoff

The pre-addition 11-page PDF (SHA-256 `f8958ba2a5b24ff55c31a1d424adeaeeac310d9de68b4b815f0163e53b9cfb25`) was rendered and every page inspected. Equations, tables, numbering, references, and glyphs were readable, with no visible clipping or overlap. Its one minor overfull-prose warning was addressed by moving the inverse-error expression to a separate display in the source revision approved above.

The source then gained the verified log-concavity corollary and the continuity clarification. Therefore the older PDF hash is **not** approval of the final rendered artifact. The final build and visual review must use the approved article hash above; record the rebuilt PDF hash separately. Any later change to mathematical formulas or claims requires renewed comparison before this approval is carried forward.
