# Implementation plan (not compiled Lean code)

## First pass: preserve the public theorem

Target `Lean/grh/src/Lib/Analytic/Landau.lean`. Leave `IsPolar`, `isPolar_primeRemainder`, and `New.LFunction_ne_zero_of_primeRemainder_le` unchanged. Place the new lemmas in a separate module during development. Keep the existing elementary `exists_mul_exp_le` or an equivalent bound. The exact final signature to preserve is the existing `New.IsPolar.landau`: for beta > 0, nonnegative real part of every residue at real x > beta, eventual upper bound, and Re rho > beta, conclude r rho = 0. No new axioms.

Suggested statements (mathematical specifications, not Lean syntax):

1. `finiteDifferenceTaylor_limit`: if H has a complex Taylor series A at zero, then for each natural n, the limit as h tends to 0 through positive real values of h^(-n) times sum_j (-1)^(n-j) choose(n,j) H(jh) is n! A(n). Prove the monomial cancellation via the forward difference operator (degree drops, leading coefficient multiplied by degree). Alternatively use the Stirling-number identity if already available. For n=0 take continuity. Use a finite Taylor truncation and little-o remainder; no differentiating the integral.
2. `realSamples_coeff_nonneg`: if the germ F near real c agrees with a convergent integral of g(v)exp(-u v) at nearby real u and g is nonnegative, then each coefficient of F(c-w) is a nonnegative real. Use finite integral linearity, binomial theorem, and closedness of the nonnegative real ray in C. Use dominated convergence for continuity at removable sample points. Existing `integrableOn_laplace_of_abs_le` handles E on the far right; the elementary exponential integral handles K.
3. `nonnegTaylor_radial`: in a ball of convergence, norm H(w) <= Re H(|w|), and Im H(|w|)=0. Use norm of a convergent series bounded by sum of norms; each coefficient is nonnegative real. Mathlib power-series-on-ball results may be reused. Prove equality of the analytic representative with the germ, not arbitrary point values of a meromorphic function.
4. `nearestPole_real_residue`: on a closed ball inside the meromorphic domain, a nonempty set of genuine poles is finite. Choose a pole of minimum distance r from c. Fill removable singularities on the open ball of radius r. Apply 3 along the ray approaching a nearest pole p and along the positive real ray; multiply by r-t and pass to the limit using the simple-pole residue hypotheses. Conclude that c-r has positive real residue, at least the norm of the residue of p. In fact this step needs only the residue limit and nonzero residue at p: the limiting inequality forces Re(res(c-r)) > 0, and its imaginary part is zero because H(t) is real. This avoids separately proving blow-up and identifying the real pole before the limit.
5. `negative_real_residue_of_pole`: construct F=K/(s-beta)-Phi. Choose real c sufficiently large with c>b and 2c(Re rho-b)>norm(rho)^2-b^2. The disk radius norm(c-rho) lies in Re s>b. Apply 4. Convert residue back to -r(c-r). The original `IsPolar.landau` is now a short corollary, with b between beta and Re rho.

For pointwise Lean meromorphic functions use `meromorphicOrderAt`, punctured neighborhood limits, and the library's analytic modification/removable singularity results; do not equate a zero residue with `AnalyticAt` for an unmodified value. If a globally filled-in representative is inconvenient, define the function on the ball by local holomorphic germ values, then show local agreement. Before committing, inspect Mathlib APIs at the project toolchain and prove the four helpers in isolation. No exact new API names or successful elaboration are asserted here.

## Second pass: real-only contract (optional)

Add a local real-sample polar predicate identical to `IsPolar` except that the transform identity is required for real u > 2, with real integral cast to C. Derive it from existing IsPolar. Generalize the replacement theorem to that predicate. In PrimeError.lean, obtain a new real-sample transform via the nonnegative sum-integral interchange of report §4, retaining the Euler series identity and residue calculation. The residue at 1 can be branched as G(1)-Re G(1); its real part is zero. Do not silently assume it vanishes. Audit other users of `LSeries_lambdaKResidueClass`, `integral_primeRemainder`, `ofReal_re_logDerivMean_one`, and `isPolar_primeRemainder` before removing or weakening anything. Preserve the old stronger predicate and old lemmas if required by another proof.

## Third pass: optional localized selector

Keep `exists_entireL_quadTwist_ne_zero` as the constructive existence input. Define `targetedTwist` as the two order conditions of report’s Targeted twist criterion. Derive it from the existing full-box selector. The contradiction follows from the rightmost-real obstruction. No independent cheaper existence proof is provided; avoid replacing the old existence theorem with an unsupported assumption.

## Acceptance gates

- Check the actual toolchain (`lean-toolchain`, `lake-manifest.json`) and work at a clean committed revision. Run `rg` for references to every declaration to be removed; note that imported names may be used via namespaces and tactics.
- Build unchanged baseline and record time, peak memory, line counts and dependencies. Use `lake build` for the full project, as specified by the repository's own instructions; preserve project flags and trust settings.
- Build new helper modules, then the original-signature replacement, then the complete original targets, then optional refactors separately. Compare `#print axioms` for endpoint and top-level theorems to the baseline; check for `sorry`, `admit`, new `axiom`, and unsafe changes. Test real-point equality at removable singularities and zero residue at 1 explicitly.
- Report net Lean lines after all required new dependencies are counted, not gross deletions. If complex-analysis API overhead makes the replacement longer, retain the conceptual proof for documentation but do not claim a measured formal saving.
- Verify that the narrower selector permits no false inference when a real negative residue occurs at exactly Re rho. Keep the original zero-free box lemma available until a genuinely cheaper selector is proved.

## Status

Source-level migration specification only. Lean was not installed in this environment; no source changes or build were performed. The accompanying exact Python tests are finite regressions, not a kernel proof.
