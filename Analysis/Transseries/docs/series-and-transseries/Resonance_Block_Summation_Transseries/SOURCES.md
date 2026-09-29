# Source provenance

Access date: 29 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit used for the direct source comparison:
`0c973d8f5e7ef4550f4df1bf486d890037fd9f14`.

The repository was read via the connected GitHub tools. No write operation
was performed. The inspected root and Transseries trees located the current
transseries corpus and its recent arrivals.

### Directly inspected comparison source

- `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/README.md`
- `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex`, source lines 180–360.

Pinned source link:
https://github.com/VladimirReshetnikov/ProveIt/blob/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex

Relevant labels: `cor:countable`, `prop:collision`, `eq:contour-transport`,
`eq:actions`, `eq:homogeneous-bound`, and `eq:tail`.

The source provides a weighted countable analytic extension and an explicit
inverse coefficient/tail calculus. It states that this is not automatically a
countable-action resurgence theorem. Its finite-action collision result uses
analytic bounded perturbation amplitudes. The present report instead cancels
unbounded individual pole residues inside finite blocks before applying the
weighted-family inverse machinery.

### Inventory and overlap check

`Analysis/Transseries/docs/series-and-transseries/README.md` was inspected,
including the discussion of recent unmerged arrivals. This was used to avoid
repeating the moving-fold, feedback-regularity, q-transition, inverse-harmonic,
and finite-action-accumulation projects. The inventory check was not an
exhaustive theorem-level audit of every recent package.

## Primary literature

1. David Sauzin, *Introduction to 1-summability and resurgence* (2014).
   https://arxiv.org/abs/1405.0356
   Used for established Borel-Laplace/resurgence background and nonlinear
   closure context. Our finite-cluster norm estimates are proved directly.

2. Carl de Boor, *Divided Differences*, Surveys in Approximation Theory 1
   (2005), 46–69.
   https://arxiv.org/abs/math/0502036
   Used as the primary reference for classical divided-difference identities.
   The contour and simplex formulas needed in the report are also explained
   and proved there in the article's own argument.

3. Stefano Marmi and David Sauzin, *Quasianalytic monogenic solutions of a
   cohomological equation* (2001 preprint).
   https://arxiv.org/abs/math/0101149
   Relevant small-divisor/quantum-logarithm context. No claim is made to solve
   or supersede its general parameter-regularity problem.

4. Stavros Garoufalidis and Rinat Kashaev, *Resurgence of Faddeev's quantum
   dilogarithm*, arXiv:2008.12465v2 (2020).
   https://arxiv.org/abs/2008.12465
   https://arxiv.org/pdf/2008.12465
   The full paper was inspected for the meromorphic Borel, pole/residue, and
   Stokes context, including its distinction between useful integral formulas
   and unsuitable product manipulations at real parameters. The report does
   not claim a new discovery of that general phenomenon and does not assert
   an unproved exact identity between its sine-product kernel and a particular
   quantum-dilogarithm normalization.

The literature check is sufficient to identify classical ingredients and
important neighboring work. It does not establish independent novelty or
exclude all prior special-function versions of the quantitative refinements.
No external PDFs or font files are redistributed in the package.
