# Lambert W

The Lambert W function enters the Fabius–Rvachev corpus through the
two-scale endpoint asymptotics and the phase-locked Richardson layer of
the exponents-and-q-series group.  The latter now runs from the exact
algebra in `LambertPhaseLockedRichardson.lean` through the fixed-order
analytic extractor in `FabiusLambertPhaseExtraction.lean` (with its
pullback, complete-homogeneous, and reciprocal-row estimate modules),
while the κ∞ decay gauge remains separate.  The endpoint programs of that volume's Parts VI–VII
and of the inverse-endpoint volume use the lower branch W₋₁ as their
canonical coordinate.  These articles treat the function itself, so they
form their own group.

Four independently written article packages arrived together on
2026-08-28 and were **merged editorially** (same day) into the single
consolidated volume:

Member: `Lambert_W_Guide/` — *The Lambert W Function: A Real-Variable
Guide* (59 pp, consolidated edition).  The most complete of the four
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
monotonicity, range, continuity) and the principal branch in
`PrincipalLambertW.lean` (defining equation on `[-1/e, ∞)` with
the branch bound `W₀ ≥ -1`, uniqueness among solutions `≥ -1`, the
branch point `W₀(-1/e) = -1`, `W₀(0) = 0`, `W₀(e) = 1`, and strict
monotonicity of the branch and of the forward map `t·eᵗ`,
continuity on the open domain, the exact image `(-1, ∞)`, and the
exact restricted image `W₀([-1/e, 0]) = [-1, 0]`, together with the
inverse-function derivative `W₀' = 1/(e^{W₀}(W₀+1))` with its strict
positivity) — the volume's central objects, kernel-verified.
The pair-level facts live in `LambertBranchDichotomy.lean`: the global
bound `-1/e ≤ t·e^t` derived from `1+x ≤ e^x` alone, the forward map
strictly decreasing on `(-∞, -1]` (the mirror of the principal-side
monotonicity), the closed value `W₋₁(-2e⁻²) = -2`, and the **branch
dichotomy**: every real solution of `w·e^w = z` is `W₀(z)` or `W₋₁(z)`
(`Fabius.eq_principalLambertW_or_eq_lowerLambertW`) — the guide's
two-branch inversion statement, kernel-verified.

The scaled integer-power profile package lives in
`PowerExponentialLambert.lean`, `PowerExponentialLambertCalculus.lean`,
`PowerExponentialLambertInverse.lean`, and
`PowerExponentialLambertFabius.lean`.  For nonzero natural power and positive
amplitude/rate it gives both real phases, their endpoint-inclusive solve
laws, exact branch images, interior derivatives and signs, and two-sided
`InvOn` laws; the unit-rate generalized coordinate and the Fabius
`(m,A,beta) = (1,1,log 2)` phase are exact specializations.  General
small-argument asymptotics for this scaled family remain open.

For the Fabius endpoint observable itself,
`FabiusLambertPhaseLockedPullback.lean`,
`CompleteHomogeneousAsymptotics.lean`,
`LambertReciprocalAsymptotics.lean`, and
`FabiusLambertPhaseExtraction.lean` prove that every fixed reciprocal
Lagrange row extracts the periodic term with a complete finite Poincaré
remainder hierarchy.  Subtracting the first `S` residuals at row order `r`
leaves `O(lambda^(-(r+1+S)))`, and the estimator converges to the prescribed
periodic value along every integer phase ray.  No convergence of the formal
infinite residual series, Bell/harmonic conversion, multiplicative
relative-error hierarchy, derivative extractor, or growing-order uniformity
is claimed.
