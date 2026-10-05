# Source and claim audit

Checked during preparation on 4 October 2026. This record identifies mathematical
antecedents and project context, not an exhaustive priority search.

## Public research sources

1. Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699 (2023).
   https://arxiv.org/abs/2311.13699
   Used to identify a documented research connection: algebraic structures subject
   to Borel/topological regularity. Its theorem concerns models of arithmetic,
   not the series-field classification developed in this manuscript.

2. Khodr Shamseddine and Martin Berz, *Analysis on the Levi-Civita field, a brief
   overview*, Contemporary Mathematics 508 (2010), 215–237.
   https://www2.physics.umanitoba.ca/u/khodr/Publications/RS-Overview-offprints.pdf
   Author-hosted published offprint. Used for the classical left-finite-field
   background. The needed algebra and completeness arguments are reproved here.

3. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
   of generalised formal power series*, arXiv:2107.03362.
   https://arxiv.org/abs/2107.03362
   Published with the shorter title recorded in the manuscript, Journal of
   Algebra 605 (2022), 339–376. Antecedent for strongly additive automorphism
   structure. No claim that this article's broader field hypotheses are identical
   to the present left-finite, ordered, coefficient-Borel setting.

4. Pavao Mardešić, Maja Resman, Jean-Philippe Rolin, and Vesna Županović,
   *Formal normal forms and formal embeddings into flows for power-log
   transseries*, arXiv:1505.05929 (2015).
   https://arxiv.org/abs/1505.05929
   Antecedent for formal normalization and flow mechanisms; not used as an
   unproved input to the simultaneous-classification theorem. The primary
   abstract was surfaced during the initial literature search; later direct
   fetch attempts failed. No unavailable full-text claim is relied upon.

5. Hassan Azad, Indranil Biswas, and Said Waqas Shah, *Lie's classification of
   finite dimensional algebras of Vector Fields in C^N*, arXiv:2605.24948 (2026).
   https://arxiv.org/html/2605.24948v1
   Section 3 explicitly reviews the classical classification on the line.
   The dimension-three and affine/projective patterns are credited as classical.
   This manuscript supplies its own valuation proof and precise exponent-orbit
   refinement, instead of invoking analytic local conjugacies in a formal field.

## Repository context

The following files were read through the GitHub connector:

- `Algebra/SurrealNumbers/README.md`
  Blob SHA: `a7ebc59ad60d52ac4448e12ea8d2385227e34031`
  https://github.com/VladimirReshetnikov/ProveIt/blob/main/Algebra/SurrealNumbers/README.md
- `Algebra/BakerCampbellHausdorff/README.md`
  Blob SHA: `e24d8fc8dbb4901bdaa9c588367e0b5ed2797451`
  https://github.com/VladimirReshetnikov/ProveIt/blob/main/Algebra/BakerCampbellHausdorff/README.md

These supply the normal-form/strong-summation and BCH project connection. Their
other mathematical claims were not independently audited, nor used as theorems
in the proof of the main classification.

The supplied LinkedIn profile was not available as a complete readable page.
No mathematical attribution or assertion of endorsement relies on that profile.

## Prior project artifacts

The user's Library supplied:

- `borel_summability.pdf`, *Borel Regularity Forces Summability*, 4 October 2026.
- `borel_conjugacy.tex` / `.pdf`, *A Divisibility Threshold for Borel Conjugacy*,
  4 October 2026. Question 14.3 asks about nonabelian Lie-group actions and
  their infinitesimal Lie algebras.

These are unrefereed AI-assisted project antecedents, not publications certifying
priority. The needed automatic-regularity and substitution facts are proved
again. The present manuscript advances the simultaneous-pair problem and the
rank-one finite-dimensional infinitesimal subproblem. It does not claim to
classify all jointly Borel actions of all connected Lie groups.

## Proof and novelty boundary

- Main scalar and pair theorems: complete written arguments in Sections 5–6.
- Nonsmoothness contrast: direct Baire-category argument in Section 7.
- Finite-dimensional Lie results: complete valuation-based proof in Section 8;
  the classical pattern itself is not claimed as new.
- Whole-field action obstruction: explicitly assumes coefficient-differentiable
  actions with Borel derivation generators. General automatic differentiability
  is listed as a further question.
- Exact finite computations: 669 passing regression assertions, recorded in
  the accompanying report. These do not verify the infinite-support or
  descriptive-set-theoretic proofs.
- No Lean verification, independent referee certification, or exhaustive
  historical-priority certification is claimed.
