# Proposed ProveIt integration

## Destination

Suggested primary directory:

`Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion/`

Copy this package intact, keeping the LaTeX source and PDF together. Add a cross-reference from the Polylogarithms research index because the normal form, integer resonance, and order-jet connections are equally relevant there. The repository was inspected at commit `6207c3d40047fd8d1400a4d509fee71c9a3a8132`; maintainers should apply current intake conventions when integrating a later revision.

## Proposed index entry

> **Boundary Completion for Quadratic Polylogarithm Feedback** (12 October 2026). Resolves the incoming boundary-feedback conjecture for `uv-v²/2 = Li_s(r exp(v))`: exact radius and unique dominant singularity for every positive order and feedback parameter; supercritical coefficient constant including integers; critical stable, logarithmic, and Gaussian regimes; convergent inverse charts and all order-three logarithmic coefficient corrections; joint order/feedback chart and fixed-order coefficient crossover. Includes proofs, source comparison, reproducible checks, and ten further research questions.

## Source cross-reference to add

The incoming archive `docs/incoming/Resonant_Polylogarithm_Transseries.zip` contains `Resonant_Polylogarithm_Transseries/article.tex`.

- Its theorem label `thm:feedback` states the correct interior result (source lines 1030–1090 in the reviewed snapshot).
- The first paragraph of `sec:future` proposes the supercritical coefficient constant and asks for all critical boundary cases (source lines 1279–1297).
- The new article's `thm:phase` proves the proposed constant and the three critical laws; `cor:physical` extends the physical convergence threshold to all `s>0`.

Suggested editorial note:

> The boundary regimes posed here are resolved in *Boundary Completion for Quadratic Polylogarithm Feedback*, Theorem `thm:phase`. With `A=ζ(s−1)` and `b=√(u²−2ζ(s))`, the supercritical equivalent is `b^(s−1)/(b−A)^s · R_b^(−n)n^(−s)`. At `b=A`, the critical coefficient scales are `R_b^(−n)n^(−1−1/(s−1))` for `2<s<3`, `R_b^(−n)n^(−3/2)(log n)^(−1/2)` for `s=3`, and `R_b^(−n)n^(−3/2)` for `s>3`, with explicit constants and convergent local charts in the new report. The original interior theorem is unchanged.

Prefer an editorial note or cross-reference that preserves historical numbering. The original open question was not a false theorem and should not be labeled an erratum.

## Antecedents that must remain credited

The generic mechanisms have close prior treatments in:

- `Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex`: the linear-tail Lagrange/probability identity, stable critical exponents, and coefficient crossover.
- `Stable_Gaussian_Endpoint_Uniform_Critical_Transseries/article.tex`: the moving-order endpoint scale, Lambert normalization, and uniform local limits for eventually exact power tails.
- The other four incoming polylogarithm ZIP articles: resonant order jets, ordinary inverse charts, complex folds, and exact exponential sectors.

The new kernel `f_u(t)=u−√(u²−2Li_s(t))` does not have an eventually exact pure-power coefficient tail plus a finite polynomial. This report proves its global endpoint continuation and nonlinear constants directly. It does not claim discovery of stable laws or pole pairing as general methods.

## Scope to preserve

1. For `s>2` and real `b>0`, `R_b` is the actual radius only at or above critical feedback. Below it, the interior-fold radius is larger, although the probability identity still uses `R_b`. Smaller values of `u` can have an interior fold without a real endpoint reference `b`.
2. The coefficient crossover fixes `s>2` and keeps `b` in a fixed positive compact interval. Its bounded normalized displacement consequence then gives `b→A`.
3. The joint local inverse chart is uniform only for compact real scaled order and feedback parameters.
4. The complex-fold theorem concerns local continued normal-form solutions. Global access from the original Taylor germ remains open.
5. Convergent analytic charts, finite asymptotic coefficient expansions, numerical checks, and formal proofs are distinct statuses.

## Suggested review order

Review `sections/02-phase.tex` first, then the critical charts and logarithmic transfer, followed by the two crossover sections. `CLAIMS.md` records theorem labels and antecedents. The numerical tables provide independent checks of the signs and constants. No changes have been made to the remote repository, and this package contains no compiled Lean claims.
