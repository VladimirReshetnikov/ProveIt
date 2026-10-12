# Additive integration plan

No repository writes have been made. The following paths are proposed destinations, not assertions that these directories currently exist.

## Suggested placement

Place this package under:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/universal-gamma-normal-forms/`

The self-contained `article.tex` may be built there directly. The short `universal_gamma_normal_forms.tex` fragment can instead be added to the canonical manuscript's normal-form chapter after its existing functional-decomposition and Gamma hierarchy definitions. It uses `ubg:integration:` labels and assumes standard AMS packages plus a host `theorem` environment.

The fragment has a compact proof structure, not the full analytic application sections. For the full theorem proof retain article Sections 2–4 or link the report. Do not copy the short proof while dropping the locality and highest-quadratic-variation hypotheses.

## Update the research ledger

Mark the affine report's question about all `[u_0^a u_1^k u_2^b u_3^2] N_m`, `b>0`, as answered by the universal formula. Its question about higher-multiplicity coefficient sectors is also answered for the standard hierarchy `A_(m+1)=u_0 A_m-D A_m`.

Record that the earlier complete `u_0,u_1,u_2` recurrence now has a finite beta-sum evaluation. Preserve the predecessor's attribution for the affine square kernel, the canonical functional complement, centering, and Appell covariance. Do not mark general profiles, arithmetic independence, or individual normal-monomial integral evaluations as solved merely because the coefficient problem is solved.

Do not change the status of Gaussian S6, revised S8, or the general unequal harmonic-tail moment-prefix rank problem.

## Formula and endpoint conventions

The full theorem's coefficient average is **half** the integral over `[-1,1]`. Its explicit-integral version therefore has `2^(2d+1)` in the denominator. The Hurwitz, Stieltjes, and Fourier transforms in the article use the **full** interval integral. Their residue is the full mass, not half the mass.

Reduce before setting high jets to zero. The normal projection is rational-linear, not multiplicative. The quadratic-background heat expression includes the scalar `exp(z/24)`. All apparent endpoint singularities are combined before spectral limits are taken.

At ordinary positive endpoints retain `H(beta)-H(alpha)`. At a fixed-coordinate finite part at zero retain `H(beta)-CT_x H(x)`; the lower constant is not generically zero.

## Proposed editorial corrections

1. In the inspected affine article bibliography, change the Guo–Regensburger–Rosenkranz page range from `456--473` to `456--471`. The primary arXiv journal-reference record verifies the latter. `affine_bibliography.patch` applies to the exact Library source basename; adapt its path only after checking the integration target. The baseline source SHA-256 is in `../data/source_manifest.json`.
2. The canonical manuscript README blob `dc0fa26d0e5c2ede56df37c5640c7319681dfd25` repeated the paragraph about the complete 1,032-input first-letter X family, rank 1,008, kernel 24. Remove the second copy only if it remains in the target revision. No automated patch to an unverified later README is supplied.

No substantive mathematical error was established in the overlapping predecessor formulas. The new theorem strengthens the scope; it is not a claim that those formulas were incorrect.

## Verification and review

Replay the scripts in the package root. Retain their rational CSV/JSON certificates and the source manifest with the report. The all-order proof is human-readable mathematics; the finite exact tests are not a Lean formalization. The numerical checks have declared local tolerances and are not interval certificates.

Before a formal repository merge, review the polynomial-background transport and highest-variation proof independently, then check whether any intervening incoming reports overlap the result. The source audit records the actual inspection limits rather than treating the moving default branch as a single frozen snapshot.
