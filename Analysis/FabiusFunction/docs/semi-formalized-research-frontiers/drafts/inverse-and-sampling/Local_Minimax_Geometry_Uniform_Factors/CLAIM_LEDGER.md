# Claim ledger

## Results proved in the article

| Claim | Location | Validation status |
|---|---|---|
| Full blockwise local minimax classification | Theorem 2.1; Sections 7–10 | Conventional upper and lower proofs; not proof-assistant checked |
| Joint maximum-loss rate | Corollary 2.2 | Consequence of the blockwise theorem |
| Localized shifted-power-sum inverse exponents | Theorem 4.1 | Counting-function/sign-polynomial proof; sharp paths in Section 8 |
| Recovery of the missing first power sum with exponent 1/(r+1) | Theorem 5.1 | Nonnegative-coefficient proof; sharp zero paths in Section 8 |
| Analytic coefficient recovery despite positive collisions | Theorem 6.1 | Polynomial implicit-function proof |
| Root-n asymptotically normal variance estimate at all-positive configurations | Theorem 6.2 | Finite-moment CLT and explicit delta-method calculation |
| One estimator adapts to every fixed stratum | Section 7 | Feasible finite-grid fitting plus localized inverse inequalities |
| Exact shifted-moment cancellation | Lemma 8.1 | Lagrange interpolation and ODE proof; finite symbolic instances checked |
| Likelihood distance from density Taylor coefficients | Lemma 9.1 | Weighted Gaussian domination and dominated convergence |
| Nonzero leading likelihood coefficients on hard paths | Sections 9.2–9.4 | Symmetric-polynomial/cumulant argument and derivative expansions |
| Explicit r=2 constants | Section 11.2 | Exact calculation using Gaussian derivative norms; numerically corroborated |

The proof numbering above refers to the delivered article. Finite checks are
not used in place of any universal proof.

## Reproduction evidence

The supporting script passes 186 exact assertions covering selected shifted
flow identities, Newton-sum cancellations, the mixed coefficient certificate,
and two explicit hard pairs. It computes four finite-window high-precision
likelihood diagnostics. The latter are not rigorous numerical error bounds.
The recorded results are in `verification_results.json`.

## Prior results credited, not claimed as new

The capacity-M global rates and detection results are prior claims of the
repository's Gaussian-confounding report. Its flat-boundary companion gives
global extensions without a positive Gaussian floor. This article does not
re-prove or audit all claims of those reports. Its proofs for the stated
positive-variance mixed-stratum model are self-contained apart from standard
analysis/probability tools. The all-zero specialization is explicitly credited.

## Claims not made

- Worldwide priority, independent peer review, or Lean/Rocq verification.
- Uniform risk constants for moving cluster gaps, growing capacity, or vanishing variance.
- Asymptotic efficiency of the explicit variance estimator.
- A practical polynomial-time solver for the full moment fitting problem.
- A classification for the unsmoothed mixed-stratum statistical experiment.
- A pointwise-at-a-singleton minimax claim: the main risks are local-uniform on fixed neighborhoods.

The eight questions in Section 13 are proposed research extensions, not theorems.
