# Proposed ProveIt integration

Baseline commit: `570b0567f311cf1890865065896be2665f469e4f`.

The repository has not been modified. This package is a proposed research continuation. A suitable new report directory is:

`Analysis/Polylogarithms/docs/reports/translation-critical-depth/`

Preserve the full package there, or follow the repository's incoming-archive procedure. Integrate selected proofs into the manuscript by topic after review. Use theorem labels instead of current chapter numbers when reconciling the sources.

## New statements and suggested destinations

| Component | Source in this package | Suggested location |
|---|---|---|
| Hurwitz translation master formula, endpoint expansion, positive kernel and Gram determinants | `article/01_translation.tex` | Integrated zeta jets / Stieltjes antiderivatives |
| Sharp Sobolev thresholds and complete shift primitives | `article/01_translation.tex` | Antiderivatives, with a spectral cross-reference |
| Gamma translation energy, strict concavity, exact maximum, odd-zeta series, polygamma derivatives, definite primitive | `article/02_gamma.tex` | Gamma integrals and Stieltjes bridges |
| Near-critical Euler reversal proof, correction, Lambert approximation, profile and derivative roots | `article/03_euler_transition.tex` | Fractional real-order Euler continuation |
| Optimal eventual sign blocks and all-order critical finite parts | `article/04_lerch_critical.tex` | Immediately after the dominant Lambert-pair theorem |
| Full Cayley ideal retraction preserving depth and exact filtered dimensions | `article/05_cayley_depth.tex` | After the existing full Cayley ideal projector |
| Source actions and research agenda | `article/06_audit_and_questions.tex` | Editorial ledger and active research agenda |

The assembled source has no cross-reference dependency on the repository: every theorem used from the baseline is recalled and cited. The detailed proof of the inherited global phase/selected-sheet theorems remains in its pinned source. Source paths and hashes are recorded in `source_provenance.json`.

## Promote the precise Euler conjecture

Pinned report path:

`Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/continuations/tetralogarithm-euler-polynomial-zeros/sections/06_audit_research.tex`

Promote **`research:conj:crossing`** to the theorem proved here as **`eutrans:thm:crossing`**. Preserve the statement's uniformity for the inner order in a fixed compact subset of `(0,infinity)` and for each fixed derivative order. The accompanying density and two-scale lemmas are essential; merely substituting into the earlier fixed-parameter expansion does not prove the joint limit.

The existing premises are in that report's `sections/03_fractional.tex` and `sections/03b_phase.tex`, including `phasefrac:thm:unique` and `phasefrac:cor:derivatives`. Those theorems remain valid. The new theorem extends their asymptotic information.

## Close two Lerch questions

Pinned report directory:

`Analysis/Polylogarithms/docs/reports/lerch-global-phase/continuations/euler-lambert-dominant-extrema/`

Its `sections/10_research_agenda.tex` asks for the least eventual block length and higher critical finite parts. These are answered by `newdiag:thm:sharp-block` and `newdiag:thm:finiteparts`.

The selected inverse sheet, dominant pair, Puiseux expansion and additive coefficient asymptotics in `sections/05_harmonic.tex` are inherited premises. Do not relabel them as new. The phase's irrationality at `A=2` remains unresolved and is unnecessary for the optimal-block theorem.

For critically weighted sums of order at least two, include the conjugate-singularity terms `newdiag:eq:E`. A subtraction containing only nonoscillatory powers would generally fail to converge. At order two, the omitted term would have size `sqrt(N)`.

## Add the Cayley refinement with its exact scope

Pinned antecedent:

`Analysis/Polylogarithms/docs/reports/fractional-cayley-scaling/continuations/golden-cayley-double-turning/sections/05_cayley.tex`

The existence of a full Cayley ideal projector, the all-depth weight-seven count `7518`, and nonmembership of the frozen S6 formal target were already proved there. The new result is a different projector with output depth no greater than input depth, plus the exact filtration.

The new identity is `Pi C = Pi`. Its image is generally not pointwise C-fixed, so `C Pi = Pi` must not be added. The endpoint map sets `z=x=0` in shuffle-polynomial coordinates; this is not a literal letter deletion or an analytic assignment to divergent integrals.

At weight seven, the K-odd exact-depth dimensions are:

`1, 34, 347, 1582, 3115, 2123, 316`.

Depth at most four has quotient dimension `1964`; the full ideal intersects the `2546`-dimensional bounded ambient space in dimension `582`. The `23`-dimensional balanced unmultiplied Cayley-row span is a different space. It does not include all product consequences.

The frozen S6 target's new normal form has 30 adapted-word terms of depth at most two and remains nonzero. The earlier 3444-term representative uses a different basis and a different section of the quotient. No support-minimality or numerical nonreduction conclusion follows from comparing those counts.

## Preserve inherited and unresolved statuses

- S4 is already proved in later material.
- The index-six and index-seven Stieltjes derivative transition counts are already proved in manuscript `chapters/09-higher-zero-transitions.tex`, label `higherzeros:thm:thresholds`. This report does not replay those inherited certificates.
- The current S6 and S8 numerical candidates remain conjectural.
- The selected-sheet accessibility of the dominant Lerch conjugate pair is already proved in the latest continuation.
- All-index Euler extremizer and indexed bulk-phase questions remain open beyond their stated proved cases.
- Formal quotient dimensions do not count independent numerical periods.

No false theorem was found in the specific latest source sections used as premises. The article records status reconciliation, a proof of the outstanding Euler conjecture, and corrections to possible overextensions of earlier methods. Existing historical error corrections in the repository's editorial ledger are not claimed as new discoveries here.

## Files and reproducibility

The article's definitions and frozen target are self-contained. No upstream Python module is needed. The Cayley code uses exact rational arithmetic; other scripts require the listed scientific Python packages. The README supplies separate exact, numerical, and Euler replays. Keep the diagnostic status attached to floating-point results and the analytic proof attached to asymptotic statements.

The supplied TeX uses labels `thm:*`, `eq:*`, `cor:*`, `eutrans:*`, `newdiag:*`, and `depthcay:*`. Before merging into the larger manuscript, prefix the generic translation/Gamma labels if the destination already uses them. Preserve the existing branch and Laurent conventions.
