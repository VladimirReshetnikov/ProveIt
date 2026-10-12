# Independent audit of the Gamma-integral basis and fixed-gap theorem

Date: 2026-10-11. Auditor: separate research agent. Audited source: `conjecture_work/GAMMA_BASIS_PROOF.md`, including optional Sections 5 and 6. This is an independent derivation check, not a machine-verified proof and not a global novelty certificate.

The working-note path above records the original audit input. Its statements and derivations are incorporated and expanded in Section 8 of the accompanying article, which is the authoritative version included in this package.

## Verdict

No mathematical flaw found in the stated Gamma-integral basis, exact normalization, boundary determinant representation, coefficient asymptotics, fixed-gap eventual nonvanishing, or first harmonic correction. The main hypotheses and the restriction to a fixed gap are essential. The argument does not establish an effective cutoff or nonvanishing at every finite pair.

## Independently checked points

1. **Formal equation and dimension.** Coefficient extraction from the cotangent equation gives the stated positive Bernoulli recurrence for every index `N > m`. The lower powers impose no hidden condition: the germ is even with zero constant term, and the apparent negative powers cancel or are differentiated to zero. The first `m` coefficients are arbitrary.

2. **Contour shifts.** Substitutions `y=x−i` and `y=x+i` put the two integrals on the bottom and top sides of the same strip. The Gamma recurrence gives the same integrand with the factor `2^(2m)`. The common Gamma factor has nearest poles at `±3i/2`, outside the strip. For sinh weights there are no enclosed poles. For tanh there are precisely the poles `±i/2`, each with residue `1/π`. The bottom-minus-top orientation has sign `+2πi`. Both residues give the stated `i 2^(2m+2) π^m cosh(t/2)` forcing term. Vertical sides vanish by uniform Stirling decay.

3. **Derivative constant and rotation.** The pole of `coth(t/2) Q^(2m)` has coefficient `2 Q^(2m)(0)`. The other differentiated product is analytic at zero. This determines the constant without an arbitrary integration term. The rotation `R(z)=i Q(iz)` gives the stated sign `(-1)^(m+1)` and factor in the exact tanh moment. In particular, the `m=1` normalization gives `R''(0)=16π`, consistent with `t_(1,1)=8π`.

4. **Positive initial determinant.** The leading coefficient of `Im(x+i/2)^(2n)` is `n x^(2n−1)`. Andreief therefore contributes exactly the product `∏ 4n/(2n)!`. Dividing each sinh column by tanh gives `v U_(k−1)(v)`, with degrees in descending order. This gives the sign `(-1)^[m(m−1)/2]` and the power `2^[(m−1)(m−2)/2]` in `K_m`. The two Vandermonde factors have the same sign at every set of distinct positive nodes. The integral is finite and strictly positive.

5. **Recurrence matching.** If `T_m` is the initial coefficient matrix, the later coefficient matrix is exactly `F_(b,m) T_m`. Dividing by its nonzero determinant gives the displayed boundary representation, including its sign. The inherited source formula matches it exactly:

   `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/harmonic-tail-gamma/sections/02_gap_four.tex`, theorem `gap:complementary`, equation `gap:complementary-formula`.

   The older Differential report uses full tail orders as subscripts of `M`; the newer report uses half orders. The article should state its convention rather than silently switching.

6. **Laplace asymptotics.** The conjugate Gamma product has no inverse first power after its leading factor. The density therefore has relative remainder `O(x^(−2))`. The supplied split at `x=N^(2/3)` gives the required absolute moment error relative to the Gamma scale without analytically continuing the unknown remainder density. The model contour shift yields the term `i m R/[2(N−m)]`. This term is essential: for even mode index `j`, the leading imaginary part is zero. The stated odd and even constants `L_j` and powers `m` and `m+1` are correct.

7. **Determinant asymptotics.** After factoring the scalar asymptotic from each column, the limiting matrix is `(x_j^i)`, with `x_j=(jπ)^(−2)`. Its Vandermonde determinant is nonzero. Its orientation sign cancels the initial determinant sign. The remaining product of signs is `(-1)^floor(m²/4)`, and the total power of `2b` is `m²+floor(m/2)`. The positive constant and the exponential factor in the notes follow exactly.

8. **Optional hypergeometric equation.** Writing `Q=(e^t−1)F` reduces the differential equation to

   `D^(2m)F − e^(2t)(D+1)^(2m)F = −c(e^t+1)/2`.

   Substituting `u=e^(2t)`, `D=2Θ` gives the notes' inhomogeneous hypergeometric equation and constant. Identification of the homogeneous generalized hypergeometric operator is classical.

9. **All-orders density and harmonic correction.** The shifted logarithmic Gamma expansion, together with

   `B_(2k+1)(1/4)=−(2k+1) E_(2k)/4^(2k+1)`,

   gives exactly the logarithmic density coefficient `m |E_(2k)|/[k 2^(2k+1)]`. Expanding `(y−i/2)^(−m−2r)` gives the stated finite formula for each asymptotic coefficient. Taking imaginary parts selects the required parity. The first relative correction to `t_(n,j)` is `d_j(d_j−1)/(4n)`.

10. **Independent derivation of κ_m.** For `V_(ij)=x_j^i`,

    `x_j ∂_(x_j) log det V = 1 + Σ_(k≠j) x_j/(x_j−x_k)`.

    At `x_j=(jπ)^(−2)` this equals

    `m+3/4+(j/2)(H_(m−j)−H_(m+j))`.

    The determinant correction is `Σ d_j(d_j−1)/4 − Σ d_j a_j`. Using `Σ a_j=m(m+1)/2` gives exactly

    `κ_m = −[m²(m+3)+e(2m+3)]/4 + Σ_(r=1)^e r(H_(m+2r)−H_(m−2r))`, `e=floor(m/2)`.

    The first four values in the notes check. Higher normalized coefficients belong to `Q[π²]`, since all additional mode-radius factors occur in even powers and the Vandermonde ratios are rational after factoring row powers of `π`.

## Scope and presentation safeguards

- The theorem proves eventual full formal rank along every **fixed-gap** ray `(p,q)=(2b−2m,2b)`, with `m` fixed and `b→∞`.
- It is different from the repository's earlier eventual theorem with the smaller order fixed.
- Neither theorem alone proves all unequal even pairs. No numerical cutoff `B(m)` is supplied by the present proof.
- The asymptotic expansions are Poincare expansions, not convergent inverse-power series and not exponentially improved transseries.
- The determinant assertion concerns rational formal coordinates. It makes no arithmetic independence assertion about the resulting special values.
- Numerical quadrature and exact recurrence checks are useful diagnostics, but the proof rests on the contour identity, the nonzero initial determinant, and the nonzero asymptotic Vandermonde.
- A limited literature search supports cautious wording such as “new relative to the inspected ProveIt sources”; it does not justify an absolute priority claim.
