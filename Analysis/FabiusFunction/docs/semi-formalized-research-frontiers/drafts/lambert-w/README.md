# Lambert W

The Lambert W function enters the Fabius–Rvachev corpus through the
two-scale endpoint asymptotics and the phase-locked Richardson layer of
the exponents-and-q-series group.  Its finite coefficient pipeline now runs
from the exact residual-moment algebra in
`LambertPhaseLockedRichardson.lean`, through the generic
complete-homogeneous/Bell dictionary in `CompleteHomogeneousBell.lean`, to
the shifted-reciprocal Bell specialization in
`LambertPhaseLockedBell.lean`.  The fixed-order analytic extractor remains
in `FabiusLambertPhaseExtraction.lean`, with its pullback,
complete-homogeneous, and reciprocal-row estimate modules, while the κ∞
decay gauge remains separate.  The endpoint programs of that volume's Parts
VI–VII and of the inverse-endpoint volume use the lower branch W₋₁ as their
canonical coordinate.  These articles treat the function itself, so they
form their own group.

Four independently written article packages arrived together on
2026-08-28 and were **merged editorially** (same day) into the single
consolidated volume:

Member: `Lambert_W_Guide/` — *The Lambert W Function: A Real-Variable
Guide* (61 pp, consolidated edition).  The most complete of the four
treatments forms the body; the unique layers of the other three (the
complete power-tower convergence theorem, inverse-Taylor corrections,
the branch-exchange involution, the transcendence theorem, a
practitioner's toolkit, further applications, and the r-Lambert
outlook) are preserved in a complements section; a four-way concordance
appendix records that the shared core agreed theorem for theorem and
constant for constant, and a corpus-role section links W₋₁ to the
Fabius endpoint theory.  The four packages’ figures, data, and
verification scripts are preserved under `Lambert_W_Guide/assets/`;
the absorbed source documents themselves are deleted after merging,
with SHA-256 provenance in the document itself (git history is the
archive).

See [`../MANIFEST.md`](../MANIFEST.md) for the group record.

The corpus formalizes the real Lambert pair: the lower branch in
`LowerLambertW.lean` (definition, defining equation, uniqueness,
monotonicity, range, branch-point continuity, and continuity on the full
domain `[-1/e, 0)`) and the principal branch in `PrincipalLambertW.lean`
(defining equation on `[-1/e, ∞)` with the branch bound `W₀ ≥ -1`, uniqueness
among solutions `≥ -1`, the branch point `W₀(-1/e) = -1`, `W₀(0) = 0`,
`W₀(e) = 1`, strict monotonicity of the branch and of the forward map
`t·eᵗ`, branch-point continuity, continuity on the full domain
`[-1/e, ∞)`, the exact image `(-1, ∞)`, and the restricted image
`W₀([-1/e, 0]) = [-1, 0]`).  The endpoint/full-domain declarations are
`principalLambertW_continuousWithinAt_branchPoint`,
`principalLambertW_continuousOn_Ici`,
`lowerLambertW_continuousWithinAt_branchPoint`, and
`lowerLambertW_continuousOn_Ico`.  The inverse-function derivative
`W₀' = 1/(e^{W₀}(W₀+1))`, its strict positivity, and the exact endpoint value
`W₀'(0) = 1` (`deriv_principalLambertW_zero`) are kernel-verified.
The pair-level facts live in `LambertBranchDichotomy.lean`: the global
bound `-1/e ≤ t·e^t` derived from `1+x ≤ e^x` alone, the forward map
strictly decreasing on `(-∞, -1]` (the mirror of the principal-side
monotonicity), the closed value `W₋₁(-2e⁻²) = -2`, and the **branch
dichotomy**: every real solution of `w·e^w = z` is `W₀(z)` or `W₋₁(z)`
(`Fabius.eq_principalLambertW_or_eq_lowerLambertW`) — the guide's
two-branch inversion statement, kernel-verified.

The exact raw second-order package is `LambertWCurvature.lean`.  Its
principal API is `deriv_principalLambertW`,
`deriv_principalLambertW_hasDerivAt`,
`deriv_deriv_principalLambertW`,
`deriv_deriv_principalLambertW_zero`,
`deriv_deriv_principalLambertW_neg`, and
`strictConcaveOn_principalLambertW`; in particular, `W₀''(0) = -2` and
`W₀` is strictly concave on the full closed domain `[-1/e, ∞)`.  The lower
API is `deriv_lowerLambertW_hasDerivAt`,
`deriv_deriv_lowerLambertW`,
`deriv_deriv_lowerLambertW_pos_iff`,
`deriv_deriv_lowerLambertW_neg_iff`,
`deriv_deriv_lowerLambertW_eq_zero_iff`, and
`strictConvexOn_lowerLambertW_left`/
`strictConcaveOn_lowerLambertW_right`.  Thus `W₋₁''` changes sign exactly at
`-2e⁻²`, with strict convexity on `[-1/e,-2e⁻²]` and strict concavity on
`[-2e⁻²,0)`.

The scaled integer-power profile package lives in
`PowerExponentialLambert.lean`, `PowerExponentialLambertCalculus.lean`,
`PowerExponentialLambertInverse.lean`,
`PowerExponentialLambertAsymptotics.lean`, and
`PowerExponentialLambertFabius.lean`.  Its second-order companion is
`PowerExponentialLambertCurvature.lean`.  For nonzero natural power and
positive amplitude/rate it gives both real phases, endpoint-inclusive solve laws,
exact branch images, interior derivatives and signs, and two-sided `InvOn`
laws.  The normalized argument is continuous
(`powerExponentialLambertArgument_continuous`), the principal phase is
continuous on the full closed value interval
(`principalPowerExponentialPhase_continuousOn_Icc`), and the lower phase is
continuous on the positive endpoint-inclusive interval
(`lowerPowerExponentialPhase_continuousOn_Ioc`).  Among nonnegative
variables, `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower` is the
exact solution iff through the peak, and
`principalPowerExponentialPhase_ne_lowerPowerExponentialPhase` makes the two
roots distinct strictly below it.  This does not classify additional
negative roots possible for even powers.

On the common smooth interval `(0,peak)`, the curvature companion proves
`deriv_principalPowerExponentialPhase_hasDerivAt`,
`deriv_deriv_principalPowerExponentialPhase`,
`deriv_lowerPowerExponentialPhase_hasDerivAt`, and
`deriv_deriv_lowerPowerExponentialPhase`.  For either phase `lambda`, the
exact formula is
`lambda * (m - (m - beta*lambda)^2) /
(x^2 * (m - beta*lambda)^3)`.  This generic module is formula-only: the
sign/zero thresholds `beta*lambda₀ = m - sqrt(m)` and
`beta*lambda₋₁ = m + sqrt(m)`, together with the resulting generic strict
shape theorems, remain open Lean work.

At zero, `principalPowerExponentialPhase_isEquivalent_rpow` identifies the
principal root equivalent `(x/A)^(1/m)`, while
`tendsto_lowerPowerExponentialPhase_nhdsGT_zero_atTop` gives divergence of
the lower phase to `+∞`.  The lower result
`lowerPowerExponentialPhase_sub_intrinsicMain_tendsto_zero` is specifically
the intrinsic-epsilon two-term expansion for
`epsilon = (beta/m)(x/A)^(1/m)`.  It does not yet give a cleaned
`L = log(A/x)` normalization or a full generic asymptotic series.

The Fabius specialization `(m,A,beta) = (1,1,log 2)` now includes the
principal phase `fabiusPrincipalLambertPhase`, the exact nonnegative-root iff
`fabiusSaddle_eq_iff_eq_principal_or_eq_lower`, strict interior distinctness
`fabiusPrincipalLambertPhase_ne_fabiusLambertPhase`, full interval
continuity in `fabiusPrincipalLambertPhase_continuousOn_Icc` and
`fabiusLambertPhase_continuousOn_Ioc`, and the zero-endpoint equivalence
`fabiusPrincipalLambertPhase_isEquivalent_id`; the lower generic phase is
identified with `fabiusLambertPhase` by
`lowerPowerExponentialPhase_one_one_log_two`.

`PowerExponentialLambertFabiusCurvature.lean` closes the classical curvature
specialization.  It defines
`fabiusLambertInflectionInput = 2*exp(-2)/log 2`;
`fabiusLambertInflectionInput_mem_Ioo` proves that this lies strictly below
the peak, and `fabiusLambertPhase_inflectionInput` gives the lower phase
there as `2/log 2`.  The module also gives
`deriv_deriv_fabiusLambertPhase`,
`deriv_deriv_fabiusLambertPhase_pos_iff`,
`deriv_deriv_fabiusLambertPhase_neg_iff`,
`deriv_deriv_fabiusLambertPhase_eq_zero_iff`, and
`deriv_deriv_fabiusLambertPhase_inflectionInput`, and proves
`strictConvexOn_fabiusLambertPhase_left` on the positive interval through
the inflection and `strictConcaveOn_fabiusLambertPhase_right` from there
through the peak.  For the principal phase, the same module exports
`fabiusPrincipalLambertPhase_eq_principalLambertW`,
`fabiusPrincipalLambertPhase_continuousOn_Iic`,
`fabiusPrincipalLambertPhase_hasDerivAt`,
`deriv_fabiusPrincipalLambertPhase`,
`deriv_fabiusPrincipalLambertPhase_hasDerivAt`,
`deriv_deriv_fabiusPrincipalLambertPhase`,
`deriv_deriv_fabiusPrincipalLambertPhase_pos`,
`deriv_deriv_fabiusPrincipalLambertPhase_zero`, and
`strictConvexOn_fabiusPrincipalLambertPhase` on the whole closed half-line
ending at `exp(-1)/log 2`, including negative inputs and zero.

Still open in Lean are both branch-point vertical-tangent limits and the
Puiseux package.  No derivative at the branch point is claimed, and the
generic square-root threshold/shape package remains open as stated above.

For the Fabius endpoint observable itself,
`FabiusLambertPhaseLockedPullback.lean`,
`CompleteHomogeneousAsymptotics.lean`,
`LambertReciprocalAsymptotics.lean`, and
`FabiusLambertPhaseExtraction.lean` prove that every fixed reciprocal
Lagrange row extracts the periodic term with a complete finite Poincaré
remainder hierarchy.  Subtracting the first `S` residuals at row order `r`
leaves `O(lambda^(-(r+1+S)))`, and the estimator converges to the prescribed
periodic value along every integer phase ray.  The new finite rewrite tranche
is recorded by
`completeHomogeneousEvalOn_shiftedReciprocal_eq_bell`,
`sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add_eq_bell`, and
`sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_bell`: the generalized
harmonic power sums become factorially weighted Bell inputs, and the exact
fixed-order residual moments become factorially normalized complete Bell
polynomials.  The direct normalized specialization uses a field with
rational-algebra structure, and the weighted moment forms assume
characteristic zero; total inversion adds no positivity or nonzero-shift
premise.  This is a finite algebraic conversion only.  No convergence of
the formal infinite residual series, multiplicative relative-error hierarchy,
derivative extractor, uniformity in growing row order or residual depth, or
new sign control at those boundaries is claimed.
