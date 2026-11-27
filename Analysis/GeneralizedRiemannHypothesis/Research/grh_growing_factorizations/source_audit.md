# Source audit and proof dependencies

Accessed via GitHub on 27 November 2026. Root path: `Analysis/GeneralizedRiemannHypothesis/` in `VladimirReshetnikov/ProveIt`, branch `main`. The vendored README identifies upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The following blob hashes were returned by GitHub when reading the files. The upstream identity of the full tree is reported by the vendored README, not independently compared byte by byte here.

| Path relative to root | Blob SHA | Use |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Pin, import status |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Build and axiom claims |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact definitions, Mathlib scope |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorems |
| `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` | Covolume cancellation |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | One-sided prime bound |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Merge scope, 131 reports / 914 results |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Section layout |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Scope, distinctions |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Source mechanism (relevant portion) |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | Full relevant factorization and small-bias arguments |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | Relevant headings |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Relevant headings |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Relevant headings |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | Relevant headings |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Relevant headings |

The article was examined via its LaTeX source, not by re-reviewing its 723-page PDF. No independent certification of all merged results is implied.

## Dependency graph

1. `Main.LFunction_ne_zero_of_half_lt_re` (global Lean declaration `LFunction_ne_zero_of_half_lt_re`) and `LFunction_eq_zero_re` provide Dirichlet GRH. The statements quantify over every positive integer modulus, including imprimitive characters; nothing about Artin L-functions of degree greater than one is needed.
2. Classical smoothed explicit formula + unit-height zero count + prime number theorem => Lemma 3.1, the uniform small-bias pool. Its selection argument uses independent Bernoulli choices and a union bound. This is an adaptation of `dir:lem:oneset`.
3. Gram/Bessel bound on words of bounded length in pairwise ratios => Lemma 4.1, order of the exceptional group J at most floor(1/a). This is the first change from the previous minority theorem; no uniform bound over all characters of lcm(q_j) is needed.
4. Unconditional integer circulation decomposition on the type-by-label table, with cycle coefficients reduced modulo exponent(J) => Lemma 5.1 and Corollary 5.2. This is the second change. It bounds the number of moves by D^2(e-1)r, with D=|J| and e the exponent of J.
5. Multinomial coefficient estimate by torus integration, as in `dir:lem:partition`, grouped by cosets of J, and a count by number of labels outside the dominant coset => Section 6.
6. Combine the Fourier tail with the occupied-fibre mass bound => Theorem 2.1, including exact support and relative equidistribution. Worst-case coset example proves sharpness; prime counting proves the growth-order limitation for the specified quota scale. Compressed type DP gives the constructive finite support test once S is provided.

## Formalization route (not a checked Lean artifact)

- Keep the vendored package as a separate Lake project with Lean 4.35.0 and its pinned Mathlib; do not assume compatibility with the ProveIt root package.
- State finite type-product repair for a finite commutative group and finite labelled objects, with equal row and column margins. Prove circulation decomposition by strong induction on the number of positive edges. Reduction mod the group exponent is a separate lemma. Then formalize the Hamming-ball covering bound by counting a finite union.
- Prove the small-bias subgroup lemma with `Finset` Gram inequalities, then define the character ratio map and its kernel. Separate the analytic prime pool lemma from these finite proofs.
- Formalize Fourier inversion and the multinomial coefficient bound separately from the analytic input. For the latter, import the upstream global GRH statements and formalize or reuse the appropriate uniform explicit formula. No Lean toolchain was available in this execution environment; exact Mathlib identifiers for the new lemmas are intentionally not guessed.

## External literature examined

- Booker and Pomerance, arXiv:1607.01557; published Proc. AMS 145 (2017), 5035–5042.
- Klurman, Shparlinski and Teräväinen, arXiv:2609.25393.
- Hughes, arXiv:2610.04678.

These address related squarefree smooth representation and subset-product covering. They do not establish priority for the new multi-label minority-density quotient law. A comprehensive literature review and independent formal verification remain outside this packet.
