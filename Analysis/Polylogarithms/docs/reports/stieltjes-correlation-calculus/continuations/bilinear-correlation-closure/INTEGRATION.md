# Suggested ProveIt integration

This is a delivery package, not a commit or an automatic patch. No live repository file was modified.

## Proposed report location

Preserve the delivered ZIP as required by the repository's incoming-report procedure. After intake review, a suitable new report directory is:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-closure/`

The report extends the single-function Hurwitz-jet and Stieltjes-antiderivative calculus. It is not a continuation of radial inequalities. Prefer a new report rather than silently replacing either an older Gamma-moment report or an incoming archive.

## Optional manuscript insertion

1. Review the proofs in `article.tex`, especially the counterterm definitions and the analytic generating theorem.
2. Copy `integration/07-stieltjes-correlations.tex` into the manuscript's `chapters/` directory.
3. Add `\input{chapters/07-stieltjes-correlations}` after the single-function Stieltjes/Hurwitz-jet calculus in `07-integration.tex`. Choose a location after the Laurent convention and classical antiderivative ladder have been introduced.
4. Link the new report in the editorial ledger and source inventory, preserving its claim-status distinctions. Add the article's classical source references to the manuscript bibliography as appropriate.
5. Run the full manuscript build and its existing tests. The delivered wrapper tests the fragment in isolation, not against an exact checked-out copy of the full moving manuscript.

All labels in the fragment begin with `corrclosure:`. Auxiliary macros begin with `\corrclosure` and are introduced by `\providecommand`. The fragment expects the parent to load AMS mathematics, theorem environments named `theorem`, `lemma`, `corollary`, and `remark`, and `hyperref` for its one reference link. These are compatible with the inspected parent preamble.

## Required editorial distinctions

- `I_mn` is an endpoint finite part or its exactly equivalent convergent subtraction. It is not a bare ordinary integral.
- The coincident product has an additional double-singularity counterterm. Directly setting a=0 in a divergent integral is not valid.
- The translated log-Gamma autocorrelation is an ordinary convergent integral.
- The coefficients are explicit zeta polynomials; no numerical independence theorem is implied.
- The symbolic generator checks finite algebra, while convergence and continuation remain analytic proofs in the article.
- Numerical quadrature residuals are not interval bounds.
- The observed mpmath canary is a method/version-specific accuracy issue, not an analytic error in the polylogarithm identity and not a demonstrated upstream theorem error.
- Preserve the upstream S4 proved status. Do not mark S6 or other remaining colored reductions as resolved by this article.

## Scope of review

Selected current manuscript sections, the incoming directory inventory, and the intake README were inspected. No binary incoming ZIP was unpacked. The final branch lookup returned `e1294e75708b84986bfdaf103892ac9ac78a0580`; earlier reads used main and are not represented as a uniform pinned checkout. See `notes/PROVENANCE.json`.
