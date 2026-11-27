# Source and dependency audit

## Repository inspection (27 November 2026)

GitHub connector read-only access was used. ProveIt commit:
`ec99bc9e223fd8ca520792464033914ede28abec`.
Base URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec99bc9e223fd8ca520792464033914ede28abec/Analysis/GeneralizedRiemannHypothesis>.

The two requested directories were listed, and selected source files, article theorem headings, and the relevant detailed proofs were fetched. The article README reported a 723-page compilation of 131 reports (914 theorem-like results). This is not an exhaustive review of those 914 results or the 300,000 lines of Lean.

| File relative to the base | Git blob SHA | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Vendoring provenance and separate Lake build. |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Scope, toolchain, reported verification. |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Mathlib-only formal statements. |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Five exported theorem declarations. |
| `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` | Main covolume comparison and cancellation of arithmetic main terms. |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | (initial excerpt inspected) | One-sided ramp bound. |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Article inventory and status labels. |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Article structure. |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Source input and proof architecture. |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Positive-filter theorem, lower bound and open question. |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Ramp explicit formula. |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Context for positive spectral techniques. |
| `Article/remarkable-results.tex` | `e7ce20d0eed0f0d0aa03656b1ba80243e746daa6` | Selected results and review policy. |

The vendoring README identifies upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026). The project pins Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The vendored development is not built by ProveIt's root Lake package. The upstream documentation reports no extra axioms and successful independent kernel checks. The independent Rubinstein verification overview at <https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/> records the original and compact-edition checks. No new Lean compilation or proof-kernel audit was performed here.

## Direct extension of the article

The decisive text is in [`rec.tex`, lines 4696–4698](https://github.com/VladimirReshetnikov/ProveIt/blob/ec99bc9e223fd8ca520792464033914ede28abec/Analysis/GeneralizedRiemannHypothesis/Article/sections/rec.tex#L4696-L4698), under the shortest-positive-averages open questions: it asks for the optimal constant in the logarithmic support of `rec:thm:logfilter`, between the Jensen lower bound and the existing construction.

| Article label | What changes in this note |
|---|---|
| `rec:lem:sepfilter` | Near-lattice phase classes permit a rectangle convolved with a very short rectangle, with half-width asymptotic to pi/cell-width. |
| `rec:thm:finitefilter` | Sort by phase and color occurrences within each cell; treat low frequencies recursively. Use a separate optimal stopband factor instead of repeated sinc factors. |
| `rec:thm:logfilter` | Match the lower bound's leading coefficient for cancellation; match the stronger coefficient including the prescribed exponential tail. |
| `rec:lem:jensensupport` | Replace circular Jensen by the slit-plane Green-function inequality: prescribed-zero cost and weighted log attenuation are additive. |
| `zer:lem:ramp`, `rec:thm:polylogavg` | Sharp leading half-width and controlled exponential moments; obtain an O_q((1+log X)/X) simultaneous averaging error. |

## Proof dependency map

1. The general spectral counting hypothesis and elementary complex analysis imply the slit-plane bound.
2. Positive interpolation + phase-bin counts + convolution + recursion imply the matching leading upper bound and bounded moment-generating functions.
3. A positive Volterra construction and classical Bernstein's inequality give the pure stopband optimum.
4. The classical Dirichlet Riemann–von Mangoldt formula supplies the spectral counting hypothesis, unconditionally; zero ordinates are real by definition. No independence, simplicity, or spacing conjecture is used.
5. The exported `LFunction_eq_zero_re` plus the ramp explicit formula puts all noncentral zero contributions on pure Fourier frequencies, yielding the prime application. This is the only use of Dirichlet GRH in the new results.

## Boundaries

- The result solves the leading-constant problem in the inspected article's precise model, including aggregate multiplicity. It does not determine the optimal bounded second-order term, the distinct-only cancellation constant, or the minimal width of arbitrary center-dependent balancing schemes.
- No arbitrary Artin, Hecke, or automorphic GRH statement is inferred from Dirichlet GRH.
- The new proof is classical mathematical prose. The numerical script is an exploratory consistency check, not a certificate for the theorem or the zeta zeros. The upstream Lean proof is not bundled or rebuilt here.
- A targeted web literature search examined classical entire-function bounds and positive/stopband filter constructions. It establishes neither exhaustive bibliographic coverage nor publication priority. The earlier article's explicit open question is the basis for the relative novelty claim.
- No repository files were modified.
