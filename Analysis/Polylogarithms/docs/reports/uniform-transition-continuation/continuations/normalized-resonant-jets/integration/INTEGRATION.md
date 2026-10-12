# Proposed integration

This is a proposed new research report, not an edit to an accepted manuscript. No repository writes were performed.

Primary destination:

```text
Analysis/Polylogarithms/docs/reports/resonant-polylog-transseries/
```

Cross-reference it from `Analysis/Transseries/docs/series-and-transseries/README.md`. Preserve the TeX/PDF pair together. All equation and statement labels begin `rpt:`.

## Mathematical placement

Theorems 2.3 and 3.2 fit beside order derivatives and Hurwitz/Stieltjes jets. Definitions of the Gamma multiplier and counterterm must be included: the normalized jet is not a raw polylogarithm derivative.

Theorems 4.1 and 4.2 fit beside differential-block and finite-difference calculus. Their minimal-node assertion is an application of Vandermonde rank; do not describe finite differences themselves as newly discovered. Retain the reduced guaranteed analytic radius after dilation.

Theorems 5.1 and 5.2, Proposition 5.3, and Theorem 6.1 fit beside coefficient-form Lagrange inversion and exact-core charts. The finite coefficient formula must not be substituted for an operator-form Lagrange identity without a separate derivation. The auxiliary pole statement does not assert global inverse continuation.

Theorem 7.1 and Corollary 7.2 connect exact half-shift arithmetic to inverse support. The inverse core depends on the jet order: the zeroth jet uses d=1, the first jet d=2. Do not compare their coefficient values while silently keeping the wrong core.

Theorems 8.1 and 8.2 provide the bounded-resonance chart and the exact half-shift order-tuning curve. This is a local theorem for the explicitly normalized family, not a solution of every existing critical-Hahn or q-transition model. The exact tuning curve depends on the tail zero and is not merely the zero of a first-order residual estimate.

## Proof status

All numbered claims have ordinary mathematical proofs in the article. They are pending independent review. `THEOREM_STATUS.json` indexes them. No Lean source or proof-assistant verification is supplied. The finite algebraic tests do not imply full analytic formalization.

A sensible formalization order is: the moment/Vandermonde theorem; centered binomial projection; coefficient-form Lagrange and support selection; the analytic realization bridge; then the Lerch normal form. Existing Bell and differential-block interfaces may be useful but were not imported or built in this package.

## Source correction

Attach the note in `CORRECTIONS.md` to the cited version of Bailey–Borwein–Crandall, rather than modifying original historical source files. The source's (49) and (54) already have the consistent minus sign; the correction targets (52).

## Suggested cross-link wording

> Resonant polylogarithmic jets admit a Gamma-normalized pure-logarithm form, optimal centered dilation filters, and convergent inverse charts. The report also proves half-shift inverse-sector selection, an exact local order-tuning curve, and a version-specific correction to a raw-order-derivative formula. Conventional proofs and finite replay evidence are supplied; no new Lean formalization is claimed.
