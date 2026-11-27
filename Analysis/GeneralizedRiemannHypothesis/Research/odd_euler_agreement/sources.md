# Source and dependency record

Repository: https://github.com/VladimirReshetnikov/ProveIt

Branch inspected: `main`, on 27 November 2026. Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. The files were read through the GitHub connector; blob identifiers pin the relevant snapshot without implying that the moving branch head remains unchanged.

| Path | Git blob or tree identifier | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Vendoring and provenance |
| `vendor/grh-lean/grh/` | `2e133df63d7f4da6b3059c4195324f8e9187ba73` | Vendored source tree |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported checks and build instructions |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact Mathlib theorem interfaces |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Five exported theorems |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | Half-plane to critical-line step |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Article scope and status |
| `Article/sections/` | `5ea418a24081239fe126bb25757cd4897d31e74a` | Section tree |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Outline and status conventions |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Main research question and analytic input |

Also consulted relevant excerpts of `src.tex` and the section headings/open questions of other sections. This was a targeted review, not a proof audit of the complete article or Lean development.

- Vendored upstream revision: `72fead102f663d5c7a407964a13dc0cf9d977207` (as reported by the vendor README).
- Lean toolchain: `v4.35.0`; Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (as reported by the readable edition's README).
- Source theorem `LFunction_eq_zero_re` supplies the Dirichlet critical-line input used in the analytic application.
- Article labels: `rec:lem:gram`, `rec:thm:qmatch`, `rec:thm:qmatchfinite`, `rec:sec:open` (item “Pooled zero statistics”).
- Published coding-theoretic dependency for equality structure: S. R. Ghorpade and R. Ludhani, *On the minimum distance, minimum weight codewords, and the dimension of projective Reed–Muller codes*, Advances in Mathematics of Communications 18 (2024), 360–382, https://doi.org/10.3934/amc.2023035 (Corollary 3.3 and Theorem 4.3). The paper includes a separate proof of the minimum-distance bound used for the main inequality.
- Classical analytic dependency: Davenport, *Multiplicative Number Theory*, 3rd edition, 2000, together with the smoothed explicit formula in `rec:lem:gram`.

The source README's verification statements are reported, not independently replicated. The new report contains a classical proof; it has not been formalized in Lean.
