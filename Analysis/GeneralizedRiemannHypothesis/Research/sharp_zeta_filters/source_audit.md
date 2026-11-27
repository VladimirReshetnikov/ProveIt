# Source audit and novelty boundary

Retrieved via GitHub connector, `VladimirReshetnikov/ProveIt`, `main`, 2026-11-27. Paths below relative to `Analysis/GeneralizedRiemannHypothesis/`. Blob IDs describe the retrieved files, not a claim that the entire mutable main branch was locked or audited. The vendor README reports byte identity of the readable upstream package to `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`.

## Vendor source

| Path | Observed Git blob SHA |
|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` |
| `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` |
| `vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean` | `5c06362a50e044d491423fb3d830bae6a50c0075` |
| `vendor/grh-lean/grh/src/Lib/Analytic/Landau.lean` | `82f02212e0b4574396bc8198c3e84b6f36df9d9b` |

Relevant declarations: `New.star_inequality` compares two bounds on a common corrected covolume, yielding `m * totalRemainder ≤ f * a * logB ^ 5`; `New.Data.primeRemainder_le` transfers it to the smoothed prime remainder; `New.eventually_primeRemainder_le_rpow` gives a one-sided power bound. `New.LFunction_ne_zero_of_primeRemainder_le` removes twisted zeros in a rectangle, uses the sign of real residues and `New.IsPolar.landau`, and concludes nonvanishing. `New.grh` exports the half-plane theorem, `New.zeros_on_line` and `New.zeta_zeros_on_line` use the functional equation, and the root-level `riemannHypothesis` supplies the only RH input used in our report. The package README reports independent proof checks with ordinary axioms; its separate Lake package is not checked by a root build of ProveIt. We did not run Lean here.

## Article

| Path | Observed blob SHA |
|---|---|
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` |

The LaTeX sources, rather than the 723-page compiled article, were used. Section headings were surveyed in the six relevant analysis/consequence sections; the specific reconstruction and ramp statements were read with proofs/excerpts. No claim is made of reading every one of the article's 914 results or the 818 vendored files.

- `rec:thm:finitefilter` uses separated color classes and convolutions.
- `rec:thm:logfilter` gives logarithmic support and fixed positive exponential stopband rate, not its sharp leading constant.
- `rec:lem:jensensupport` gives the lower bound with coefficient 1/2 for zeta.
- `rec:sec:open`, item “Shortest positive averages,” asks for the optimal support constant between the Jensen lower bound and the construction.
- `rec:thm:polylogavg` gives simultaneous prime-ramp averaging on a polylogarithmic scale range with an unspecified exponent.
- `zer:lem:ramp` provides the underlying ramp explicit formula, with an O((1+log x)/x) remainder.

This report gives a different construction with sharp leading half-width for zeta exact cancellation; it also shows the full fixed-rate stopband question cannot have leading coefficient 1/2. The bounds do not determine the exact fixed-c tradeoff, and do not solve the constant for general Dirichlet families. The zeta prime-ramp average additionally keeps the residue at s=0 exactly and integrates the contour error against a uniformly dominated density.

## Literature check

Targeted web searches for compact positive quadrature at zeta zeros, theta kernel Fourier positivity, and gap-free exponential-polynomial extrapolation did not identify a matching sharp support theorem. Classical related ingredients: Titchmarsh–Heath-Brown, *The Theory of the Riemann Zeta-function* (2nd ed., 1986); Nazarov, *Local estimates for exponential polynomials and their applications to inequalities of the uncertainty principle type* (1994); DLMF 25.10, https://dlmf.nist.gov/25.10. The report derives its extrapolation bound directly rather than relying on Nazarov's theorem. Priority in the general literature is not certified.
