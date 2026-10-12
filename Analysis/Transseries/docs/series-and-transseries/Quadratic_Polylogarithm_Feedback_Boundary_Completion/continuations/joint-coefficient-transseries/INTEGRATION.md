# Proposed ProveIt integration

## Status and destination

This package is a standalone research contribution, **Uniform Coefficient Transseries across the Polylogarithmic Order-Three Resonance**. Its proofs and the proposed repository amendments below are submitted for independent intake review. These notes do not record a completed repository integration or an accepted audit.

The comparison snapshot is ProveIt commit `8f5afd4d7565df808359f6a0c22f87f79a119bb9`, inspected on 12 October 2026. The audit concerns the relevant sources in `Analysis/Polylogarithms`, `Analysis/Transseries`, and the three incoming archives present at that commit. It is not an audit of the entire repository. Source identities and hashes are recorded in `PROVENANCE.json`.

Recommended destination for the complete directory:

```text
Analysis/Transseries/docs/series-and-transseries/
    Polylogarithmic_Joint_Coefficient_Transseries/
```

Keep the master TeX, its section files, bibliography, PDF, verification programs, numerical records, figures, and documentation together. The primary entry point is `article.tex` and its compiled `article.pdf`. The label-based review map is `THEOREM_LEDGER.md`.

All changes proposed in this file are **unapplied**. In particular, this package does not replace a predecessor report, change historical theorem numbering, modify incoming archives, or declare the collective Polylogarithms manuscript updated.

## Relationship to the existing material

The closest predecessor is:

```text
Analysis/Transseries/docs/series-and-transseries/
    Quadratic_Polylogarithm_Feedback_Boundary_Completion/
```

Its `sections/05-order-crossover.tex` treats a joint local inverse chart; its `sections/06-coefficient-crossover.tex` treats the coefficient law with order fixed. Question Q1 in `sections/07-verification-research.tex` explicitly asks for a joint coefficient theorem as the order approaches three and the feedback varies. The new report addresses that question, including all fixed logarithmic corrections. Its main new estimate is `thm:all-orders`, supported by `lem:local`, `thm:scale`, and `lem:fourier-tail`.

The predecessor's boundary classification, fixed-order coefficient results, physical threshold, convergent inverse charts, and existing intake audit remain independent results. In particular, retain `INTAKE-PROOF-AUDIT.md` and the prior reconciliation records. The new proof supplies uniformity that was not asserted by the fixed-order theorem; it does not identify an error in that theorem.

The following Polylogarithms chapters are relevant comparison points:

```text
Analysis/Polylogarithms/docs/manuscript/chapters/01-quadratic-feedback.tex
Analysis/Polylogarithms/docs/manuscript/chapters/01-lambert-moments.tex
Analysis/Polylogarithms/docs/manuscript/chapters/01-resonant-jets.tex
```

The marginal all-order Gamma-moment polynomials already appear in the repository. The exact identity `D_j = Q_j(-log 2)` in `eq:matching` is an equivalence and a normalization check. It should be described as Lambert resummation and extension to the moving-order/noncentral setting, not as an independent first derivation of the marginal coefficients.

The earlier `Stable_Gaussian_Endpoint_Uniform_Critical_Transseries` and `Confluent_Critical_Transseries_Exponent_Two_Boundary` reports supply linear-tail antecedents. Their leading moving-order conclusions and first central corrections retain their original scope. The quadratic composition changes infinitely many Taylor coefficients, so an eventually exact power-tail hypothesis does not literally cover it. The positive analytic composition theorem in this package proves the needed nonlinear extension directly.

The endpoint section supplements:

```text
Analysis/Transseries/docs/series-and-transseries/
    Polylogarithm_Resonance_And_Inverse_Transseries/
    polylogarithm_resonance_and_inverse_transseries.tex
```

That predecessor already gives noninteger inverse charts (`prop:noninteger`), a real-order univalence result (`lem:univalence`), and an integer-order cut-modulus estimate (`lem:cutgap`). The new section extracts the exact local ramification classification, constructs a convergent chart at reciprocal orders, and identifies an obstruction to extending the cut-modulus estimate. It preserves the predecessor's integer coefficient theorems. The separate `Resonant_Polylogarithm_Transseries` report and its inverse/Borel results retain their independent scope and intake status.

## Proposed index and cross-reference entries

After intake, an entry in `Analysis/Transseries/docs/series-and-transseries/README.md` could read:

```markdown
- [Uniform coefficient transseries across the polylogarithmic order-three resonance](Polylogarithmic_Joint_Coefficient_Transseries/article.pdf)
  ([source](Polylogarithmic_Joint_Coefficient_Transseries/article.tex),
  [theorem ledger](Polylogarithmic_Joint_Coefficient_Transseries/THEOREM_LEDGER.md)):
  a joint moving-order and moving-feedback coefficient theorem with all fixed
  logarithmic corrections, positive relative transition windows, and local
  reciprocal-order inverse charts. Continues Q1 and part of Q2 of the quadratic
  boundary-completion report; qualifies the proposed real-order extension in
  Q9 of the polylogarithm inverse report.
```

A cross-link in `Analysis/Polylogarithms/README.md` could read:

```markdown
- [Joint coefficient transseries and reciprocal inverse endpoints](../Transseries/docs/series-and-transseries/Polylogarithmic_Joint_Coefficient_Transseries/article.pdf):
  a Transseries companion to the quadratic-feedback, Lambert-moment, and
  resonant-jet chapters. The marginal Gamma moments are matched exactly;
  collective-manuscript incorporation requires its own editorial intake.
```

For an eventual manuscript intake, add a dated record to `Analysis/Polylogarithms/docs/manuscript/EDITORIAL-LEDGER.md` and a cross-reference from `Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/RESONANT-INVERSION-INTAKE.md`. The latter currently distinguishes audited sector results from inverse and Borel branches awaiting separate audits. A link to this package must preserve that distinction; this package does not audit all those branches. The natural manuscript split is a coefficient continuation after the quadratic-feedback material, an exact matching reference in the Lambert-moment chapter, and a separately scoped local endpoint/order-jet discussion.

## Proposed Q1 status update

**Target:** the first research question in `Quadratic_Polylogarithm_Feedback_Boundary_Completion/sections/07-verification-research.tex`, currently headed “Joint coefficient asymptotics as both the order and feedback vary.” Append a dated status paragraph, preserving the original question and its historical statement of what the predecessor proved.

**Proposed text, not applied:**

> **Status: resolved in the compact joint window by the companion report _Uniform Coefficient Transseries across the Polylogarithmic Order-Three Resonance_.** For `L = log n`, real `s = 3 + epsilon`, bounded `lambda = epsilon L / 2`, and feedback `b` in a compact positive interval, Theorem `thm:all-orders` proves the joint coefficient law and every fixed logarithmic correction. Its error is absolute and uniform over all lattice locations; on compact standardized locations it yields a relative Gaussian limit. The elementary scale is `B_0^2 = n L phi(lambda)/(2b)`, with `phi(lambda) = (1-exp(-lambda))/lambda` and its removable value at zero. Equation `eq:elementary-first` supplies the first correction in that scale. The exact scale is the unique solution with `B > 1` of the paired Gamma–zeta equation, and equations `eq:Lambert-scale`–`eq:matching` give its marginal Lambert form and exact agreement with the prior Gamma-moment coefficients. The proof establishes uniform Fourier domination through the colliding poles; it does not obtain joint uniformity by substituting a moving order into the fixed-order theorem. The truncation order is fixed, and no uniform claim for unbounded `lambda` is made.

The labels in this proposed paragraph refer to the **companion report**. If the paragraph is converted to TeX, use a bibliographic citation or explicit report/section reference until external-document labels have been configured. Do not introduce unresolved cross-references into the predecessor.

## Proposed Q2 status update

**Target:** the second research question in the same file, “Relative matching in expanding crossover windows.” Preserve the request for the largest positive and negative ranges.

**Proposed text, not applied:**

> **Status: partially resolved on the positive side.** Under the compact moving-order and positive-feedback hypotheses of the companion report, Theorem `thm:positive-windows` proves the relative approximation `B P(X_n=m) ~ g(xi) + q xi^(-3)`, uniformly for `r_L <= xi <= L^M`, where `M > 0` is fixed and `r_L -> infinity`. Theorem `thm:wing-lambert` locates the Gaussian–power transition by an explicit lower-branch Lambert expression and proves the normalized profile `1 + exp(-tau)` in its bounded transition coordinate. Corollary `cor:supercritical-matching` recovers the known supercritical amplitude in this approaching-critical overlap. The theorem does not determine the largest possible positive window, reach fixed supercritical feedback, establish growing negative relative windows, or match the interior-fold exponential factor. These parts of Q2 remain open in this treatment.

The exact Lambert center is preferable to replacing it solely by `sqrt(2 log log n)`: the latter drops the lower-order displacement needed to state the transition profile correctly. The all-lattice absolute theorem alone is insufficient for relative tail statements; the positive kernel-tail lemma and a sufficiently high fixed truncation order provide the additional argument.

## Proposed Q9 caveat and endpoint amendment

**Target:** paragraph 9, “Global geometry beyond integer orders,” in `Polylogarithm_Resonance_And_Inverse_Transseries/polylogarithm_resonance_and_inverse_transseries.tex`. The relevant preceding results are `prop:noninteger`, `lem:cutgap`, and `prop:delta`.

**Proposed text, not applied:**

> **Local qualification and obstruction.** For every `1 < s < 3/2`, the upper-bank value satisfies
> `|Li_s(exp(u)+i0)| = zeta(s) + Gamma(1-s) cos(pi(s-1)) u^(s-1) + o(u^(s-1))`
> as `u` decreases to zero. The displayed coefficient is negative, so the cut-modulus inequality used for integer orders fails in this real-order interval. This obstructs a blanket extension of that particular argument. Separately, the inverse endpoint is holomorphic at every reciprocal order `s = 1 + 1/m`, `m >= 2`; Theorem `thm:ramification` of the companion report gives the full minimal local ramification classification. These are local statements. They neither locate the next global inverse singularity nor determine the exact range of a global endpoint-circle theorem. The existing integer-order cut-modulus and radius theorems are unaffected.

This is a correction to an overbroad **possible extension**, not a counterexample to the printed integer theorem. Do not mark Q9 globally solved. Local removability at the positive endpoint does not exclude another inverse singularity of equal modulus, and the cut-modulus calculation by itself does not determine the Taylor radius of an analytically continued inverse germ.

## Scope safeguards for incorporation

No false printed theorem was established in the coefficient sources used by this report. The warranted amendments are the explicit research-status updates, the reciprocal-order exception, and preservation of parameter and branch restrictions.

The following distinctions should survive any condensation into the collective manuscript:

- **Scale branch:** uniqueness is asserted for `B > 1` at sufficiently large `n`; it is not a claim of uniqueness among all positive roots.
- **Endpoint reference and radius:** `R_b = exp(-(u-b))` is the exact normalization in the coefficient–probability identity for every `b > 0`. It is the coefficient radius on the endpoint-controlled side `b >= A`. For `b < A`, the predecessor's interior-fold radius is larger.
- **Uniformity:** the main theorem holds for compact real `lambda`, compact positive feedback, and each fixed truncation order. It does not cover `b -> 0`, unbounded `lambda`, or truncation order growing with `n`.
- **Positivity:** the general outer-function result assumes nonnegative Taylor coefficients, a uniformly positive linear coefficient, and a uniform holomorphic endpoint margin. Local Taylor algebra alone does not replace the global Fourier estimate.
- **Convergence:** the scale chart and reciprocal inverse chart converge as holomorphic germs in their independent variables. The coefficient expansion is asymptotic to every fixed inverse-logarithmic order. No convergence, optimal truncation, or summability of its infinite formal sum is proved.
- **Verification:** the finite symbolic identities, independent coefficient recurrences, and high-precision diagnostics support normalization and implementation checks. They are not a substitute for the analytic proofs, interval certificates, or a Lean formalization.

The article's final research section gives concrete continuations of the unresolved directions. Existing research questions outside the stated compact Q1 window, the stated part of Q2, and the local Q9 qualification should retain their prior status.
