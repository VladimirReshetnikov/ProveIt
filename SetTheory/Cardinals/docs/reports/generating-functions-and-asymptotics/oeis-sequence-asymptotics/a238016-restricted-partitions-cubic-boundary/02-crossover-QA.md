# Verification and production record

This is an author-side review of an AI-generated manuscript, not an independent
peer review or proof-assistant certificate.

## Mathematical checks performed

1. Re-derived the exact centering from
   `1/(1-exp(-z)) = exp(z/2+h(z))/z` and checked all factorial and Gaussian
   prefactors. The quadratic amplitude retains the m-dependent centering term.
2. Checked the exact finite-saddle cumulant signs against numerical counts.
3. Audited the outer-arc estimate for extremely small t: reserving the j=1
   factor yields `t * O(log m) * exp(-c m)`, avoiding a nonuniform comparison
   with a principal integral of size `t/sqrt(m)`.
4. Used the scaled local coordinate w=z/s to remove apparent derivative
   singularities as the continuum saddle s tends to zero.
5. Checked the all-order Gaussian operator at s=0 against reciprocal Stirling
   coefficients, so E_j(0)=0 is not inferred from numerical small-s values.
6. Derived the centered m^(5/2) necessity by subsequences, not merely along
   exact power-law inputs.
7. Checked the square-root endpoint constant in D and used it only to prove
   infinitely many nonzero Taylor coefficients, not an unproved all-sign claim.
8. Checked forward/inverse substitution and the nonvanishing inverse Jacobian.
   Implicit-function arguments are applied to finite truncations, not to a
   purported convergent infinite asymptotic expansion.
9. Kept smooth inverse errors separate from integer threshold rounding.
10. Preserved finite-size data whose second-transition sign is not yet at its
    limiting value; no numerical observation is substituted for a proof.

## Executed computational checks

`data/verification_summary.json` records PASS:

- 4,017 exact arithmetic assertions;
- four exact symbolic assertions;
- ten numerical profile assertions;
- 46 independently computed sample counts;
- maximum m=96, maximum N=268566;
- 55-digit mpmath diagnostics, not interval-certified.

The symbolic and numerical execution logs are included. No proof assistant
was run. The uniform asymptotic remainder constants were not numerically
instantiated or independently certified.

## Document checks

- Built the self-contained article with pdfLaTeX, with repeated passes to
  resolve internal references and bibliography labels.
- Final PDF: 20 pages, A4, searchable text, no external figures required.
- Final log contains no LaTeX warnings, overfull boxes, undefined references
  or citations, multiply defined labels, or hyperref warnings.
- Rendered all 20 pages to images and inspected contact sheets for page layout.
- Inspected detailed pages containing the entropy coefficient table, inverse
  formulas, and numerical-error table. Re-rendered after final wording changes.
- No clipping, overlapping equations, missing glyphs, or table overflow was
  observed in the inspected renders.
- No font files or third-party full-text papers are included in the package.

## Known limits

The article is a research manuscript. Its ordinary mathematical proofs remain
subject to expert review. The source audit is bounded and does not establish
worldwide priority. Fixed-order expansions are not claims of convergence,
optimal truncation, or a complete resurgent transseries.
