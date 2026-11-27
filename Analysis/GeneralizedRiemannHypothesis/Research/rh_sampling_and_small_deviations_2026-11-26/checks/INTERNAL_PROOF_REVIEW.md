# Internal mathematical cross-checks

Reviewed 26 November 2026.

These notes record additional AI-assisted reasoning checks performed while
preparing the two papers. They are not external peer review or a formal
proof-assistant certificate. The complete arguments are in the LaTeX
sources and PDFs. Finite computations are supplementary checks.

## Cubic sampling and its obstruction

The following points were checked in a separate reasoning pass.

1. **Convexity coordinate and sign.** The function
   \(S(1/u)=\sum_n a_n(1/n-u)_+\) is convex. The reciprocal-coordinate
   interpolation weight is
   \(\theta_h(y)=(1-e^{-y})/(1-e^{-h})\). Subtracting the logarithmic
   main term gives a nonnegative gap envelope
   \(J_h(y)=h\theta_h(y)-y\).

2. **Cubic cost.** Direct integration gives
   \(I(h)=h^2/(1-e^{-h})-h-h^2/2=h^3/12-h^5/720+O(h^7)\).
   Comparing second derivatives with parabolas proves the stated
   two-sided bounds for \(0<h\leq1\). The Mellin weight varies by a
   bounded factor on each such gap, justifying the discrete budget.

3. **Landau comparison.** The transform of the nonnegative difference
   \(H-E\) must be singular at a finite convergence abscissa. A putative
   singularity to the right of the proposed boundary would have
   nonpositive residue. A negative residue contradicts positivity of the
   transform on the real axis; zero residue is removable. Initial
   absolute convergence and local integrability are stated explicitly.

4. **Zeta normalization.** The Laurent expansion at \(s=1\) cancels both
   polar terms of the normalized transform. A zero \(\rho\) of
   multiplicity \(m\) has residue \(m/[\rho(1-\rho)]\), which cannot
   vanish. The Abel-limit argument correctly fixes the integration
   constant at \(-1-\gamma_E\). The derivative identity is stated
   almost everywhere, and local absolute continuity permits its
   integration for every endpoint.

5. **Sampling geometry.** For the exact power grid \(x_j=j^p\), the
   convergence threshold is \(p(1-\beta)\leq2\). An asymptotic
   equivalence \(x_j\sim j^p\) alone is deliberately not asserted to
   control exceptional gaps. Geometrically separated blocks of length
   \(X^\alpha\) give the boundary \(3\alpha-2\).

6. **Positive coefficients.** The bump derivatives satisfy the stated
   bounds. Consequently \(7/(16x)\leq F''(x)\leq25/(16x)\).
   The tent-kernel identity for discrete second differences proves
   \(0<a_n<4\) for every coefficient, not only those checked numerically.

7. **Exact observations and density.** Integer interpolation gives
   \(R(n)=r(\log n)\) exactly. Outside the designated bumps the
   observations vanish. The deleted count is
   \(O(X^{(2+\beta)/3})\), so the retained integers have natural
   density one. The error between the interpolant and the continuous
   bump is \(O(x^{-2})\).

8. **Meromorphic continuation.** Taylor expansion of the compact-bump
   transform yields geometric denominators
   \(1+\exp(\beta-s-j\delta)\). Distinct \(j\) give distinct vertical
   pole lines, so their residues cannot cancel. The rightmost poles
   are \(\beta+(2m+1)\pi i\), with residue \(1/140\). The interpolation
   correction is holomorphic for \(\Re s>-1\), and no pole is real.

9. **Sharpness.** Exceptional cubic energy converges precisely for
   \(\sigma>\beta\). For a proposed power \(p>3\), one may choose
   \(\beta_0\) strictly between
   \(\max(0,\beta-(p-3)(1-\beta)/3)\) and \(\beta\).
   Every modified budget then converges to the right of \(\beta_0\),
   while nonreal poles still lie farther right. The ordinary unit-gap
   contribution converges as well, since \(2-p<0<\beta_0\).

All identified precision edits were incorporated. In particular the
exceptional-gap counterexample is stated for \(5/6<\alpha<1\).
Its coefficients are bounded positive real weights, with no claimed
multiplicativity or Euler product. The Dirichlet application explicitly
reuses the upstream arithmetic twist-selection theorem.

## Small deviations from zeta and Dirichlet zeros

The second paper was checked independently against the following issues.

1. **Product and random sum.** The zero-count asymptotic makes the sum
   of reciprocal squared ordinates finite. This establishes almost
   sure convergence of the gamma sum and the exact Laplace product.
   Exponential tilting preserves independence and changes each rate
   to \(\gamma_j^2+t\).

2. **Mean and variance.** Differentiating the stated asymptotic gives
   the displayed tilted mean and variance with the correct signs.
   The hypotheses on the remainder through its second derivative
   suffice; the Fourier argument does not require an unstated third
   differentiated remainder bound.

3. **Quantitative density approximation.** With \(n=u\log u\), the
   normalized largest summand scale is \(O(n^{-1/2})\).
   The zeros with ordinates between \(u\) and \(2u\) supply a global
   characteristic-function bound of the form
   \((1+c w^2/n)^{-c'n}\). The Taylor expansion on the central
   frequency range and this global tail bound give a uniform
   first-order Edgeworth error \(O(n^{-1})\).

4. **CDF as well as density.** The odd first Edgeworth correction
   vanishes at the mean. Integrating in the CDF boundary layer gives
   the same relative error \(O((u\log u)^{-1})\). A weak central limit
   theorem alone would not justify the claimed asymptotic; the paper
   supplies the stronger quantitative estimate.

5. **Leading saddle versus exact saddle.** Their difference is
   \(O(1/\log u)\). The resulting changes in the action and prefactor
   are \(O((u\log u)^{-1})\), smaller than the isolated \(1/(48u)\)
   relative correction. The displayed Lambert-W constants, powers,
   and logarithmic limit agree with this calculation.

6. **Dirichlet completion.** Conductor and parity constants were
   checked from Stirling's expansion. Dividing out the central zero
   of order \(m\) produces the required even product. The first
   nonzero central coefficient is positive under the stated
   zero-location assumption. No simplicity or central nonvanishing
   hypothesis is silently used.

The numerical Fourier integrals in the accompanying script are
exploratory floating-point checks with a finite cutoff. They are
not interval-certified and are not used in either proof.

## Source and priority checks

The source audit pins the inspected GitHub revision and records the
selected file hashes. It is not a full rebuild of the upstream Lean
development. Neither new paper is itself formalized in Lean.

The papers credit the already-established convex interpolation,
fourth-power sampling, Landau principle, reciprocal-xi probability law,
and saddlepoint method. Especially close sources are Setiawan's
25 November 2026 preprint and Sra's 2 November 2026 version 3,
Appendix C.17. Targeted searches did not find the exact combined
statements proved here, but this does not certify historical priority.
