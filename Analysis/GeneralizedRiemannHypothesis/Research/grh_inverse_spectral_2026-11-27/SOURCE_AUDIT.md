# Source audit (2026-11-27)

Read-only GitHub connector retrieval on `main` of `VladimirReshetnikov/ProveIt`, under `Analysis/GeneralizedRiemannHypothesis/`. Blob SHA values below identify the retrieved source versions; no repository modifications made.

- Upstream pinned grh-lean commit: `72fead102f663d5c7a407964a13dc0cf9d977207` (per vendor README, 25 November 2026).
- Lean `v4.35.0`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (verified against toolchain and Lake manifest).
- Directory tree identifiers: vendored `grh` `2e133df63d7f4da6b3059c4195324f8e9187ba73`, Article sections `5ea418a24081239fe126bb25757cd4897d31e74a`.

| Path | Git blob SHA | Use |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | import and build scope |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | reported checks, theorem names |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | exact exported propositions |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | input theorem |
| vendor/grh-lean/grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 | symmetry argument |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | theorem `grh`, outline |
| vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 | `star_inequality`, outline |
| vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean | 5c06362a50e044d491423fb3d830bae6a50c0075 | one-sided Landau criterion |
| vendor/grh-lean/grh/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | audit script |
| vendor/grh-lean/grh/lean-toolchain | a6aff065db2882c535684f8c5bcd4f16e9a23915 | pinned version |
| vendor/grh-lean/grh/lake-manifest.json | 4fb97032cff9044f1ad40f17668f4fcb8ec6d2c7 | pinned Mathlib |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | merge scope and status |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | structure |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c | taxonomy of earlier results |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | architecture, headings |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | graph-coupled subsection (proof inspected), headings |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | related recovery headings |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | related arithmetic headings |
| Article/sections/spn.tex | 886e8716472aa82fd45ff68da03be946e9dbd3da | related matrix headings |

Additional targeted text searches of `zer.tex`, `rec.tex`, `li.tex`, `ana.tex` for inverse spectral, principal minor, switching and related terms. The sections were not exhaustively reviewed and the compiled article was not analyzed; the LaTeX source was used instead. The upstream README reports the five theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; it reports independent checker acceptance. No Lean executable was available in the working container, and neither the upstream proof nor the new theorem was kernel-replayed here.

## Reproduce upstream audit
From the vendored `grh` directory (not ProveIt root):

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

The source theorem actually used is `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`. It includes imprimitive characters but the new result uses only primitive nonprincipal ones. No GRH for Artin or general automorphic L-functions is used. See also https://klein.mit.edu/~drew/shortgrh/ for reported independent verification files.

## Formalization roadmap (not verified Lean code)
1. Import `Main` in a separate Lean package pinned to the vendored toolchain and expose the half-plane theorem. Establish the primitive completion as an entire real-phase function and connect its zero divisor to the half-plane statement.
2. Prove absolute convergence and uniqueness of polynomial-coefficient Dirichlet series with a common unbounded logarithmic factor. For the top homogeneous form, use multiplicative convolution on squarefree integers, Dirichlet primes in reduced classes and character orthogonality.
3. Establish Hadamard product/order estimates for the completion and finite-order entire quotients. Obtain the strict logarithmic derivative imaginary part from the real zeros, and expand the coupled determinant in principal minors.
4. Formalize the strip maximum-modulus argument with exponential damping, the rational obstruction and the Rouché/compactness passage. This analytic infrastructure is the principal remaining proof-engineering cost.
5. Formalize the finite matrix reconstruction by induced cycle expansion and spanning-tree sign propagation; the finite exact checks in `verify.py` do not replace that proof.
