# Source inspection and status

Accessed 27 November 2026 via the GitHub connector, using the requested `main` paths in `VladimirReshetnikov/ProveIt`. These are read-only inspections; no repository changes were made. Blob IDs identify the returned versions, not a claim to have captured an atomic main-branch commit.

Root: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis

| Relative path | Git blob SHA | What was inspected |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | upstream pin, separate Lake package, no build during vendoring |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | five statements, build procedure, claimed axioms and checks |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | full proposition statements; imports Mathlib |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | full five exported theorems |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | functional-equation step from half-plane nonvanishing |
| `vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean` | `5c06362a50e044d491423fb3d830bae6a50c0075` | statement and proof of one-sided prime remainder criterion |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | five `#print axioms` commands; not locally run |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | merged report counts and scope; not independent review |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | structure of article |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | status conventions and subject map |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | labels `src:thm:dgrh`, `src:sec:mechanism`, source scope and proof strategy |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | headings and `dir:lem:bias`, `dir:lem:oneset`, product and partition results, `dir:thm:signs` |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | headings, `rec:cor:dict`, `rec:thm:stable`, `rec:thm:operatorinverse` |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | headings of prime race, spectral and graph-coupling results |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | headings of integral frames and matrix statistics |

The vendor README pins upstream `lsernau/grh-lean` at `72fead102f663d5c7a407964a13dc0cf9d977207` and reports byte identity for its 818 files; that identity was not independently checked here. Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are reported upstream. Independent checks of this shorter proof are documented at https://math.mit.edu/~drew/shortgrh/ . Neither the full upstream proof nor the new argument was rebuilt here. The underlying formal theorem is Dirichlet GRH, not a statement about general number-field or automorphic L-functions.

## Novelty boundary

The direct predecessor is `dir:lem:oneset`: a fixed-bias sample of distinct primes, proved by smoothed character sums and independent Bernoulli selection. The new sampling lemma retains the bias parameter explicitly and includes the diagonal entries of the Gram matrix for a mixed-conductor primitive dictionary. The earlier `rec:cor:dict` separates single characters with corruption tolerance; `rec:thm:stable` addresses corrupted residues of zero-related observations. The new theorem handles arbitrary sparse complex mixtures through a convex objective, proves stability for compressible coefficients, and matches a worst-case universal obstruction from a cyclic packet of primitive characters. The classical ingredients (explicit formula, concentration, and finite Fourier uncertainty) are not claimed as new. This was a targeted source and literature check, not a comprehensive priority search.

External references: Montgomery–Vaughan, *Multiplicative Number Theory I* (2007), chapter 13; Tao's [254A notes](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/); Donoho–Stark [uncertainty principles](https://doi.org/10.1137/0149053); Jao–Miller–Venkatesan's GRH Cayley expander paper. The latter and Donoho–Stark are contextual predecessors, not inputs for the finite-dimensional proof.
