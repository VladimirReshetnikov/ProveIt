# Source audit (27 November 2026)

The two specified paths were retrieved using the GitHub connector from the `main` branch of VladimirReshetnikov/ProveIt. The following Git blob identifiers record the specific file contents returned; a tree listing was also inspected. This is a targeted interface and relevant-section review, not a full audit of 818 Lean files or 914 article results.

All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`.

| Path | Git blob SHA | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Imported upstream commit and separate build |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported kernel checks, theorem scope, build instructions |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Mathlib proposition types |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorem declarations |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | Functional equation transfer from half-plane statement |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | Inspected imports and theorem headers for one-sided bound and `grh` |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Scope and verification disclaimer |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Section structure |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Context and status taxonomy |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Selected theorem headings and source architecture |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | Detailed reading of `dir:sec:products` |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Selected headings |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Selected headings |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | Selected headings |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Selected headings |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | Selected headings |
| `Article/remarkable-results.tex` | `e7ce20d0eed0f0d0aa03656b1ba80243e746daa6` | Targeted keyword scan |

Vendor README states upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean v4.35.0. These pins and build/check claims are reported by the repository; no local build/replay was performed. Lean is not installed in this environment. The new proofs use only Dirichlet GRH (not Dedekind or nonabelian GRH) for the all-moduli branch. The other branch is unconditional.

## Dependency graph

- `Statements.lean` + `Main.lean`: precise Dirichlet GRH interface -> classical prime character sum bound (Jao–Miller–Venkatesan, degree 1) -> all-moduli moment lemma.
- Multiplicative large sieve -> exceptional-set moment lemma (independent of GRH).
- Prime number theorem + either analytic moment lemma -> uniform quadratic estimate, using the article's finite-group tools reproved in the note.
- Finite character duality / Parseval + swap correction -> quotient law and relative typical counts.
- Elementary counting -> sharp lower threshold.
- Hoeffding without replacement + quadratic estimate + TV hybrid -> disjoint-block theorem.

The closest article statements are `dir:lem:bias`, `dir:lem:circle`, `dir:thm:quotient`, `dir:thm:short`, and `dir:cor:almostshort`. The new work addresses a different norm, not an improvement of the source's all-residue guarantee. The joint disjoint-block proof goes beyond the single-product law. A targeted literature search located the papers listed in the bibliography; it is not an exhaustive priority search.
