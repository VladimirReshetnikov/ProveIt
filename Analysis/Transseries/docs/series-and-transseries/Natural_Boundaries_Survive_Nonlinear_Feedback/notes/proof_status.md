# Proof status and mathematical audit

## What the article proves

Theorems 1.1 and 1.2 are the headline results. Their natural-boundary component is established independently of summability theory in Sections 2–7. The positive quadratic summation component uses the classical Nevanlinna–Sokal theorem and the convolution/Lagrange inverse construction in Section 10. This dependency is explicit.

The proposed additions relative to the directly reviewed predecessor are the moving-curve asymptotic theorem, the implicit natural-boundary theorem, its forward-boundary and robustness consequences, and the negative answer to angular summability. The general-degree positive remainder-majorant formula and its optimization extend the predecessor's quadratic estimate. The fixed Fourier transform, principal-part extraction, tree enumeration, and Laplace summation tools are classical.

> **Editorial note (ProveIt, 2026-09-29).** For d = 2 the moving-curve theorem, the natural boundary and the negative answer to angular summability are not new to the repository: the earlier-filed package `../../Natural_Boundaries_Quadratic_Exponential_Feedback/` (batch 49; its `thm:main` and `thm:rigidity`) proves them independently, with explicit constants. They are new for integer d >= 3. See the editorial note after `thm:quadratic-main` in the article.

## Load-bearing proof checks

1. **Formal and analytic existence are separate.** Formal recursion is coefficientwise finite. Analytic realization is constructed only on a closed left half-disc, by a uniform contraction. No unjustified product-neighborhood analyticity at the origin is used.
2. **Moment poles really are nonremovable.** Distinct Fourier modes have disjoint pole progressions. At least one Fourier coefficient is nonzero. Removing closest principal parts leaves a strictly larger circle on which Cauchy estimates apply.
3. **The coefficient estimate is global in its summation indices.** The falling-factorial estimate holds all the way to the endpoint. It yields a two-index exponential majorant. The proof does not interchange limits in a sum justified only for fixed indices.
4. **The quadratic motion factor cannot vanish.** It equals exp(a h'(0)/2). Higher-degree holomorphic motion is lower-order at this scale.
5. **Tied nearest poles are not ignored.** Their dth powers are distinct for d=2, and for d>=3 under the stated smallness hypothesis. A Cesaro mean-square limit yields a factorially growing subsequence.
6. **The moving curve is hypothetical.** The proof assumes continuation of the implicit root, then applies the theorem to that holomorphic curve to obtain a contradiction. It does not claim the implicit root's actual boundary jets obey the same asymptotic formula.
7. **Density is used only after pointwise obstruction.** Nonzero roots at rational imaginary points are obstructed first. Isolated forcing zeros do not prevent density. The openness of any hypothetical continuation then excludes every point of the arc.
8. **The forward boundary transfers through a nonzero derivative.** The small inverse has derivative uniformly near one, so it is locally univalent up to the boundary. An extension of its inverse would invert back to a forbidden extension.
9. **All block regroupings have absolute majorants.** Tree counts control both the expansion and substitution into the nonlinear equation. The remainder estimate remains valid on the imaginary boundary.
10. **Fine and angular summation are distinguished.** Fine summation uses a fixed-width tube; angular summation would give a physical sector of opening greater than pi and would cross the proved natural boundary.

## Explicit limitations

- No Lean formalization, proof-assistant verification, or independent peer review was performed.
- Global originality and publication priority were not established.
- The natural boundary is a local arc, not a claim about a globally maximal domain or the artificial circular edge of the half-disc.
- For d>=3, the sufficient moving-curve hypothesis |q_0|<exp(-d) is not asserted optimal.
- For d>2, no unsupported identification of the literal solution with every generalized summation procedure is made.
- Entire Borel transforms do not imply angular exponential bounds. The paper proves failure of each sector-wide bound, not a pointwise growth law on every nonreal ray.
- The optimized bound controls a positive majorant, not the actual signed least error from below.
- Finite exact tests and floating-point tests are evidence about the implementation and displayed examples; they do not prove the infinite analytic theorems.

## Verification actually executed

`data/verification.json` records 324 exact rational comparisons at degree 24 for d=2,3,4, with tree blocks through degree 10. Independent constructions check both inverse compositions, the inverse kernel identity, and block-to-Taylor conversion. The displayed quadratic coefficients agree with `data/coefficients.csv`.

The full run also records ten moving-curve ratios, four rational-boundary roots, 352 Gauss magnitude checks, and one tied-pole mean-square diagnostic at 110 decimal digits. No interval certification is claimed. The numerical residual and the mathematical truncation certificate are different notions of error.

The PDF was compiled in three passes and every page was rendered and visually inspected. Build validation is recorded separately.
