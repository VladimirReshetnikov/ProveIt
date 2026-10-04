# Source provenance and comparison scope

Research and repository comparison date: 4 October 2026.

## Repository sources

Repository: https://github.com/VladimirReshetnikov/ProveIt

The pinned comparison revision returned by GitHub code search was:
`6cb1d86f19ebf9f54c8d985b141b84233b6eab66`.

The review was targeted. It did not verify the entire repository or the full
consolidated volume. Directory/tree reads established surrounding packages;
full README reads and a contiguous article excerpt established the principal
comparison. Some fetches used the default branch; code-search matches supplied
the pinned revision. The displayed radius gap was consistent across them.

1. `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/README.md`
   - Read the scope, status, exact-radius limitation, and editorial overlap notes.
   - It expressly leaves open exact equality between the complex Taylor radius
     and the real fold at each sufficiently large finite core value.
2. `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex`
   - Fetched the contiguous region beginning around source line 700, including
     normalized analytic hypotheses, the outer Lambert approximation, theorem
     `thm:radius`, its complete proof, and moving-fold expansions.
   - The bound `(1-vartheta_g)/e <= R_g <= q_c(g)` and warning about the exact
     nearest singularity are the comparison target.
   - The fold expansions in the new report are credited to this earlier work;
     their exact-radius interpretation is the new consequence.
3. `Analysis/Transseries/docs/series-and-transseries/Moment_Determinacy_Nonlinear_Transseries/CLAIM_LEDGER.md`
   and `moment_determinacy_transseries.tex`
   - Inspected code-search passages explicitly distinguishing the asymptotic
     radius from exact nearest-complex-singularity information.
   - No claim to have read the full article.
4. `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`
   - Read substantial returned material at the pinned revision to establish the
     consolidated source location and the distinction between formal algebra
     infrastructure and full complex-analytic formalization.
   - The consolidated 720-page article was not read in full.

No repository file was changed or committed. The ZIP is a standalone report.

## External primary sources

David Sauzin, *Nonlinear analysis with resurgent functions*, Annales
scientifiques de l'Ecole normale superieure (4)48 (2015), no.3, 667-702.
- https://arxiv.org/html/1212.4477v4
- https://www.numdam.org/articles/10.24033/asens.2255/
- https://doi.org/10.24033/asens.2255
Read the relevant nonlinear-closure statements, particularly the resurgent
implicit-function and tangent-to-identity inversion setting. This supplies
established background, not a claimed new closure result in this package.

NIST Digital Library of Mathematical Functions, Section 4.13, Lambert W.
- https://dlmf.nist.gov/4.13
Used for the classical Lambert branch, coefficients, and square-root model.

Joris van der Hoeven, *Complex transseries solutions to algebraic differential
equations*, author-hosted manuscript.
- https://www.texmacs.org/joris/osc/osc.html
Used for the warning that complex oscillatory composition needs compatible
restrictions and is not solved merely by adjoining complex constants.

Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
University Press, 2009.
- https://ac.cs.princeton.edu/home/
The official companion site identifies the text and its singularity-analysis
chapter. The article uses the classical algebraic-singularity transfer theorem;
no priority claim is made for that theorem or its basic coefficient formula.

## Scope of originality statements

The principal proposed contribution is the explicit positivity-free critical-
circle argument, exact selected radius, and its application to the inspected
repository gap. All standard tools are credited. A complete independent
literature-priority assessment has not been performed. The twelve proposed
research questions are not all represented as pre-existing published problems.

No external PDFs, book chapters, font files, or source-paper copies are included
in the archive. The bibliography and this note identify the sources instead.
