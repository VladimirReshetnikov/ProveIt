# Sharp Euler-factor agreement for cubic and quintic character packets

Research note, 27 November 2026. Read `paper.pdf` (compiled from `paper.tex`). The proof establishes the exact minimum disagreement density for equal-size products of Dirichlet L-functions from groups of exponent 3 and 5, and a lower bound with many sharp tiers for arbitrary odd prime exponent. It also gives a rigidity theorem for cubic extremizers and GRH-based finite detection.

## Reproduce

- `pdflatex paper.tex` three times (standard TeX Live, amsmath, amsthm, lmodern, hyperref, geometry, booktabs, microtype).
- `python verify.py` with Python 3.10+ and NumPy; the included `verification.txt` is the output of the executed test. All computations are exact integers. Exhaustive tests translate pairs so one member of the first packet is zero; duplicate representatives are possible and the counts are not claimed to be counts of translation orbits. Constructive tests cover primes 3 through 31 and lifts for primes 3, 5, 7.
- The finite tests validate instances; the general theorem uses the classical projective Reed–Muller minimum-distance theorem and the proof in the PDF. No Lean proof of the new result is included or claimed.

## Provenance

Read through GitHub connector from `VladimirReshetnikov/ProveIt`, ref `main`, under `Analysis/GeneralizedRiemannHypothesis/`. The following blob SHAs identify the actual consulted versions (not commit IDs):

| File | Git blob SHA |
|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` |
| `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` |

The vendored README identifies upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`, with Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The statement and the listed source interfaces were inspected; the entire 818-file development was not rebuilt, and the entire 723-page article was not audited. The new density results are unconditional; the prime estimates use Dirichlet GRH and standard explicit formula machinery. No other GRH is asserted. The prime bound has a weight-dependent implicit constant, not a numerical one.

The article explicitly poses the extension to odd prime order in `sections/rec.tex` (Open questions, Pooled zero statistics). This report resolves the minimum-density question for exponent 3 and 5; it does not classify the full agreement spectrum or prove sharpness for all other exponents. A targeted literature search found the classical code-distance theorem but not the exact packet theorem. Priority remains to be established by fuller literature review.
