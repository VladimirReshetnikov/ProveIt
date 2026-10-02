# Integrated mathematical verification

Manuscript: *Limiting amplitudes for corner polyhedra and Schnyder labelings*

Review date: 2 October 2026

## Conclusion

The integrated addendum passes this mathematical review. No unresolved mathematical error or missing hypothesis was identified in its stated results or their integration with the unchanged Foundation.

The reviewed argument establishes positive finite constants κ_P and κ_S such that

p_n ∼ κ_P (9/2)^n n^(-α_P),

s_n ∼ κ_S (16/3)^n n^(-α_S),

where α_P=1+π/arccos(9/16) and α_S=1+π/arccos(22/27). These are the full equivalents stated in Fusy–Narmanli–Schaeffer, Conjecture 25. The equivalent for the rigid-surface sequence has amplitude (16/19)^3 κ_S. The limits hold for every sufficiently large integer time, without a congruence restriction.

The positive amplitude formulas, their explicit universal Brownian factors, and the Lambert-W centering with a vanishing-width two-ceiling threshold bracket are also supported by the proof.

This is mathematical review with exact computational corroboration. It is not machine formal verification, external journal peer review, or a determination of publication priority.

## Exact sources covered

- addendum.tex
  SHA-256: 33219bb0fbff40ceeb70b6a34f666ef20cff17e265665a5babbd3af8fc819523
- foundation/article.tex
  SHA-256: 849e515056a5b296221d6fe1a0ca09c1a7fd78a19d776256ee25143070128bb2

Both documents contain their mathematical text and bibliographies directly; there are no further TeX mathematical includes. The accompanying JSON receipt binds these sources, the supporting scripts and check outputs, and the Foundation manifest. It identifies the delivered PDF without treating its visual layout as part of this mathematical review. A mathematical source change requires revalidation.

All 30 files of the included Foundation match the original package and its hash-bound receipt. Its statements that amplitude convergence lay outside its scope are accurately identified as describing the earlier note; the new addendum proves the stronger limits separately.

## Principal integration checks

1. **Models, indexing and coordinate frames.** The physical P time, aggregate S time, shifted S boundary, endpoint weights, and n+1 S aggregate offset match the Foundation. The physical quadrant C is distinguished from the cycle-whitened wedge K. Outer and inner domain shifts are applied before whitening and are exact on each relevant lattice coset.

2. **Boundary-shift lemma.** The fixed-width strip contributes O(m^(-1/2)(log m)^(p−1)) to the killed harmonic expectation. The unconditioned exponential tail controls the complementary p-th moment, including its tail boundary term. The fixed-shift comparison uses the uniform V/u limit as boundary distance tends to infinity and the bound on ∇log u; it does not assume that points remain in a fixed interior angular sector.

3. **Valid-cycle harmonic sandwich.** The pointwise P_b ≤ D ≤ P_0 comparison concerns complete marked cycles. The decreasing D^mV limit is finite and harmonic by dominated convergence. The fixed-initial-time inner/outer survival and endpoint brackets have polynomially integrable majorants. Their width vanishes by the boundary-shift lemma, establishing both exact cycle survival constants and the common endpoint law.

4. **Exact counted time and endpoint parity.** The two clock bounds and positional oscillation bound are unconditional. They do not assume independence between duration and displacement. The complete-cycle sandwich gives full counted-time constants, including the factor 2^(p/2). The corrected definitions select i(a) and i(b) separately; in the S bridge the forward harmonic function is even-return and the reverse one is odd-return. All required positive entrance paths are valid.

5. **Killed local convergence.** The unrestricted functional CLT is justified by the bounded-corrector martingale or by regeneration and deterministic limiting time change. The Hunt exit decomposition uses the free local theorem only while the remaining time is bounded away from zero. Exit-functional continuity, disappearing overshoot, compact exit-position truncation, and reversed late-exit control justify the limiting integral. The statement allows every integer sequence m_n/n → t>0, covering the exact thirds split. Its compact uniformity includes all endpoint parity pairs.

6. **Fixed-thirds limit.** Both finite endpoint measures have weak convergence and convergent masses. Uniform local convergence handles compact interior sets; the global O(1/n) kernel bound handles their complements, using tightness and zero limiting boundary mass. The factor two is the physical lattice covolume, and the two side measures contribute the factor 3^p. The positive integral is finite and strictly positive.

7. **Explicit Brownian constants.** The Bañuelos–Smits kernel citation was checked against the primary PDF, including its one-half-Laplacian convention. The addendum consistently uses physical Lebesgue densities, u(r,φ)=r^p sin(pφ), and physical whitening Σ^(-1/2). The Gamma factors, survival constant, entrance-law semigroup calculation, and determinants 7 and 80/9 are correct. Pulling the cycle harmonic functions back to physical coordinates gives the stated factor 4/[θΓ(p+1)sqrt(det Σ)]. The added counted-time harmonicity assertion follows from the one-step survival recursion and its polynomial/exponential-moment majorant.

8. **Enumeration amplitudes.** The P endpoint sum has a summable geometric majorant. The S aggregate offset and fixed shifts yield the multiplier 361/192 from its fixed-endpoint amplitude. The rigid relation is a signed convolution; its summable majorant and exponentially negligible polynomial correction justify the factor (16/19)^3.

9. **Inverse statement.** W_(-1) selects the large model solution. The additive terms −α log(log μ)−log γ have the correct signs and normalization. Uniform tail control of the relative logarithmic error gives the stated shrinking two-ceiling bracket. It does not imply unconditional exact rounding, and the manuscript does not claim such rounding.

## Independent reproducibility run

The top-level scripts/run_all.py was rerun successfully after inspection. It:

- verified all 30 Foundation files and the earlier mathematical receipt without modifying them
- passed the exact Brownian/Gamma, determinant, amplitude multiplier, convolution-majorant, and Lambert inverse algebra checks
- replayed all four Foundation programs in an isolated temporary copy
- matched the four substantive Foundation JSON result files byte for byte

The checks corroborate formulas and indexing. The infinite-time limits and limiting interchanges rest on the mathematical arguments, rather than extrapolation from finite tests.

## Limits of the result

The amplitude constants are characterized by positive harmonic and heat-kernel expressions. Their numerical values, quantitative convergence rates, higher coefficient corrections, and an exact universal rounding rule are not established. These limitations are preserved throughout the integrated manuscript.

The published inputs remain explicitly credited: Fusy–Narmanli–Schaeffer for the counting models, Denisov–Wachtel for the iid cone harmonic and survival results, and Bañuelos–Smits for the Brownian cone kernel. The proof does not assume a general cone local theorem for the original two-state walk.
