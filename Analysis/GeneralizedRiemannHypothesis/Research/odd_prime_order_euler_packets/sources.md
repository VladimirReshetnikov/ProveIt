# Source manifest

Snapshot: `VladimirReshetnikov/ProveIt` commit `64f3896557566342bc28ed309513a2b762568866` (branch main retrieved 2026-11-27).

Base: https://github.com/VladimirReshetnikov/ProveIt/tree/64f3896557566342bc28ed309513a2b762568866/Analysis/GeneralizedRiemannHypothesis

| File (relative to base) | Git blob SHA / relevance |
|---|---|
| `Article/README.md` | `8605e05e4715d9e142b08a458e7cee7226b59874`: 131 reports, 723 pages; merge, not independent review |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017`: `rec:lem:gram`, `rec:sec:qmatch`, `rec:thm:qmatch`, `rec:thm:qmatchfinite`, `rec:sec:open` |
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa`: upstream pin and build status |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef`: exact propositions |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600`: exported theorem statements and immediate proofs |

Additional files inspected from `main` during retrieval:

- `vendor/grh-lean/grh/README.md`: reported toolchain Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; claimed kernel and independent checker results.
- `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean`, blob `97f83ab52b2feb420e952a2722b4cef454b9e579`: `star_inequality` and input architecture (first 150 lines).
- `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean`, blob `99e5240de112527b739068b692e5007720d310c1`: one-sided analytic remainder bound.
- Article introduction and headings/open questions of several sections were inspected to choose a nonduplicative direction. The full 723-page article and the entire 818-file Lean development were not independently audited.

Upstream vendor pin: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh (25 November 2026). According to the vendor README, this is a byte-identical copy; that statement was not independently verified for all 818 files.

The relevant Lean statements are `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` and `LFunction_eq_zero_re : DirichletLZerosOnLine`. These cover all positive moduli; the half-plane statement excepts the principal pole. The new results require no further RH for other L-functions. The only GRH-dependent input is the usual smoothed prime character sum estimate, as proved in Article `rec:lem:gram`.

## Literature context

- Davenport, *Multiplicative Number Theory*, 3rd ed., 2000.
- Martin and Walji, *Distinguishing finite group characters and refined local-global phenomena*: https://kimballmartin.github.io/papers/dist-artin.pdf
- Walji, *Matching densities for Galois representations*: https://doi.org/10.1090/proc/12996
- Matoušek, Přívětivý and Škovroň, *How many points can be reconstructed from k projections?*: https://doi.org/10.1137/080715706
- *The second and the third smallest arrangements of hyperplanes in finite projective spaces*: https://doi.org/10.1016/j.ffa.2015.10.001

The targeted search did not establish priority over all finite geometry, tomography, coding theory, or analytic number theory literature. The claimed advance is the particular exact density regimes, equality cases and effective reconstruction theorem, compared with the open question in the pinned Article.
