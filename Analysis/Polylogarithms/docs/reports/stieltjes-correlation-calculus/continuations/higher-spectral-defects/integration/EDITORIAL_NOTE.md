# Proposed integration

Suggested destination:
`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/higher-spectral-defects/`.

Preserve the existing quadratic-spectrum report. Add a sibling continuation
and cross-reference its Section 7.6 as follows:

- Question 2: explicit all-order representation, resonant Stieltjes terms,
  second-order local/nonlocal separation, and universal vanishing criterion
  proved in this continuation.
- Question 7: two-mass second derivative and full confluent expansion proved;
  the second-derivative formula extends to any number of quadratic masses for
  even polynomial weights.
- Question 1: finite polylogarithmic-integrand representation at every
  nonpositive spectral integer supplied. The smallest-function-algebra and
  possible finite-elimination questions remain open.

No change is proposed to S6, revised S8, rejected frozen S8, or arithmetic
independence statuses. The first-jet anomaly and finite first-jet polylogarithm
formulas remain attributed to their sources. No false first-derivative theorem
was identified; `CORRECTIONS_AND_GUARDS.md` lists safeguards instead of
inventing errata.

`manuscript_fragment.tex` is a compact insert with labels `hsd:int:*`.
Its short proof explanations refer to the full report for convergence,
resonance, and branch details. It assumes the manuscript's ordinary theorem
and corollary environments and amsmath/amssymb. `bibliography_entry.tex` gives
an entry to add to the existing bibliography, not a second bibliography
for insertion verbatim into the chapter.

No automated patch or repository write has been applied.
