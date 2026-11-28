# Source audit

Repository consulted via the GitHub connector on 27 November 2026. The source tree is actively evolving; the blob hashes below identify the particular files read. This is a targeted audit, not a complete check of the hundreds of research reports or the underlying formal proof.

Base path: `Analysis/GeneralizedRiemannHypothesis/` in [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).

| Path relative to base | Blob SHA | Role |
|---|---|---|
| `README.md` | `7aa9ee91a8e41fdfeb62d46656b3bfed5d228b09` | Scope and pin of imported proof |
| `Article/README.md` | `c9fe005bd5cbdee34dbcfacf1d5127a59ba46d0d` | Merged article and status conventions |
| `Article/sections/intro.tex` | `d543c0b87abe04495e25b806dcc5b2df9b6f2ff0` | Transfer architecture |
| `Article/sections/src.tex` | `b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8` | Direct target: `src:cor:gramrank`, `src:q:gram` |
| `Research/gram-euler-and-zero-filters/gram/gram.tex` | `6e1445ffc7c50ce73e85e00ad57b4750e2f5bff7` | Existing precise rank-two result |
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Upstream provenance and separate build |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorem names |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact scope of Dirichlet GRH |
| `vendor/grh-lean/grh/src/New/Reduction/Lattices/TwistedLattice.lean` | `c6eacd876cd9b12bf9ded06150eedbdda966435b` | `covolume_add_index_nonneg` |

Upstream pin: [lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh). Its statements concern zeta and Dirichlet L-functions. This packet does not enlarge the scope of those statements or assume them.

The article's rank-two contraction gives `E_r(n) >= (2 kappa + o(1)) n^2 binom(n,r)` for fixed r, and asks even for the correct higher-rank order of the normalized mean. Our result supplies the matching exponent `2r-2` for that mean. The old rank-two leading constant is not altered.

## External comparison

- B. Kriepke, G. M. Kyureghyan and M. Schymura, *On the size of integer programs with bounded non-vanishing subdeterminants*, JCTA 212 (2025), 106003. [DOI](https://doi.org/10.1016/j.jcta.2024.106003), [arXiv:2309.03772](https://arxiv.org/abs/2309.03772). Question 3.4 asks whether the fixed-rank generic column number has order `Delta^(1/(r-1))`. The earlier upper exponent is `2/r`. The exact-Delta formulation matters and is addressed explicitly.
- B. Kriepke and M. Schymura, *On generic Delta-modular integer matrices with two rows*, SIAM Journal on Discrete Mathematics (2026). [DOI](https://doi.org/10.1137/25M1745878), [arXiv:2502.15394](https://arxiv.org/abs/2502.15394). Related rank-two work, not a dependency.

The literature search located the published question and related work. It is not sufficient to certify historical priority or absence of an independent solution.
