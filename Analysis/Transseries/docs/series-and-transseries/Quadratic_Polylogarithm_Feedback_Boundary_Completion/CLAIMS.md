# Result and source ledger

All “proved” statuses below mean an analytic proof is supplied in `article.pdf` and its LaTeX source. They do not mean proof-assistant verification or publication-priority certification.

| Label | Result | Relationship to earlier work |
|---|---|---|
| `thm:phase`, item 1 | Positive germ, exact interior radius, square-root coefficient law | Reproduced and credited to incoming `thm:feedback` |
| `thm:phase`, item 2 | Exact supercritical radius, unique dominance, `b^(s−1)/(b−A)^s` coefficient constant | Proves the explicit candidate in incoming `sec:future`, including integer orders |
| `thm:phase`, item 3 | Complete critical stable, marginal-logarithmic, finite-curvature laws | Completes the incoming nonlinear boundary question; general phase mechanisms are classical and present in the repository |
| `cor:physical` | Physical evaluation threshold for every positive order | Extends the source's `0<s≤2` restriction using the boundary theorem |
| `thm:chart-low` | Convergent two-coordinate inverse with polynomial sectors and finite extraction | Nonlinear critical chart; linear-tail Hahn charts are antecedents |
| `thm:chart-three` | Exact Lambert core and convergent marginal correction chart | Lambert inversion is classical; the `5/2` core constant and feedback correction are model-specific |
| `thm:chart-high` | Higher-order convergent power/log charts, sharp logarithmic degree | Related ordinary inverse charts already exist; the quadratic critical model is treated here |
| `thm:all-logarithmic-coefficients` | Every order-three logarithmic coefficient correction | Finite exact prescription; explicit first two corrections independently checked |
| `thm:joint-crossover` | Exact convergent local inverse chart with varying order and feedback | Extends the repository's endpoint scaling to the nonlinear model with explicit joint feedback profile |
| `prop:critical-support` | Parity restriction and exact first exponential coefficient | Model-specific consequence of the exact analytic chart |
| `thm:local-complex-fold` | Shifted local fold beyond nonzero complex profile zeros | Local normal-form result only; related ordinary inverse folds are already in the incoming collection |
| `prop:poisson` | Exact finite recurrence, Lagrange identity, compound Poisson representation | Classical mechanism, explicitly credited |
| `thm:coefficient-crossover` | Uniform lattice local limit on positive compact feedback sets; compact-window coefficient law | Direct proof for this nonlinear family; general stable/normal local limits and the linear-tail analogue preexist |

## Claims explicitly not made

- No new general theorem of stable probability, singularity analysis, or resurgence is claimed.
- Publication priority for every exact nonlinear formula has not been established by the focused literature search.
- The audit is not a line-by-line certification of the full Polylogarithms manuscript or Transseries collection.
- The incoming interior theorem is not an error; its boundary restriction was explicit.
- The local complex fold is not asserted to be a dominant singularity accessible from the original Taylor germ.
- The fixed-order coefficient theorem is not asserted to remain uniform when the order varies with `n`; Q1 gives a proposed next target.
- Absolute local-limit errors are not promoted to relative large-deviation estimates.
- Numerical residuals and symbolic checks are not interval certificates or Lean proofs.

## Review findings incorporated into this version

The phase theorem, the logarithmic transfer, the joint chart, and the coefficient Fourier proof were independently reviewed. This led to an explicit compactness condition `b_n∈J` in the coefficient consequence, a restricted class for the displayed transfer operator, and clarification that possible poles of Lambert-chart coefficient functions do not prove global inverse singularities. The final joint chart allows both signs of the bounded feedback displacement and proves the corresponding physical-root selection. No newly confirmed false theorem in the inspected incoming articles is reported.
