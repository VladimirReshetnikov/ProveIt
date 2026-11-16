# Verification status

## Completed in this package

- Full human-readable mathematical report compiled to a 70-page PDF.
- Residual compilation theorem, boundary discharge theorem, demand stabilization, finite viability, stable observations, height/list conversion, and cubic bisection arguments written in detail.
- Exact Python reference implementation for graph residuals, capped demand closure, finite viability, stable observations, finite height maxima, and rational cubic bisection.
- 13 Python regression tests executed successfully.
- Demo JSON regenerated from the reference implementation.
- PDF compiled by `latexmk`/`pdflatex`.
- PDF opened by PyMuPDF, preflighted, rendered to 70 PNG pages at 120 DPI, and visually inspected through contact sheets and selected full-size pages.
- Source audit pinned to the inspected public repository head.

## Supplied but not compiler-checked

- `lean/CIFER/ObjectCompiler.lean`
- `lean/CIFER/ResidualGraph.lean`
- `lean/CIFER/DemandClosure.lean`
- `lean/CIFER/Relational.lean`
- `lean/CIFER/ApplicationTargets.lean`

No Lean executable was available in the authoring environment. These files are a detailed integration outline and proof-composition prototype. They are not claimed to elaborate.

## Not claimed

- No completed `Prf PRAAx` derivation of the cubic inverse theorem.
- No completed embedded Booleanization or bounded-search library.
- No general effective Faltings or Siegel height bound.
- No general rational-cover producer for Mordell-Weil descent.
- No full effective Chebotarev, Siegel-Walfisz, or Bombieri-Vinogradov producer.
- No exact branch selector through arbitrary collisions without a positive gap.
- No claim that finite Python tests prove a universal theorem or object-theory derivability.

## Trust boundary

The mathematical report proves generic theorem schemas assuming the declared local embedded derivations and finite producer contracts. A closed formal result requires actual `Prf PRAAx` values for every local node and every residual boundary. Host execution alone does not satisfy that requirement.
