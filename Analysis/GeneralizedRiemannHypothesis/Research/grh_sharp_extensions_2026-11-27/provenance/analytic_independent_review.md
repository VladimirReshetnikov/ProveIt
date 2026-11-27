# Independent source and proof review

## Pinned sources

The ProveIt article was inspected at commit
`22e5c8b7dda558fd9a50b61465483cb4c0433694`, with section tree
`4085d6415cdf1d217fe0abf98d7555f0e9966b3a`.

Canonical source:

https://github.com/VladimirReshetnikov/ProveIt/tree/22e5c8b7dda558fd9a50b61465483cb4c0433694/Analysis/GeneralizedRiemannHypothesis/Article

All 21 section source files were retrieved, and inventories and open
questions were examined. The detailed review focused on the source
mechanism, analytic criteria, spectral recovery, matrix statistics, and
torsion selection. This is not a claim to have independently checked all
760 results in the 621-page merged article. Its README itself describes the
article as a merger rather than an independent review.

## Closest existing results

* `ana.tex`, theorem `ana:thm:binomial`: the filter
  `A_1^r A_sqrt(2)^r` has `(r+1)^2` normalized observations,
  `(r+1)(r+2)` distinct ramp observations, and error
  `O(log(r)/sqrt(r))`. In terms of a sample budget N this is
  `O(log(N)/N^(1/4))`. Every fixed filter retains one-sided detection.
* `ana.tex`, question `ana:q:family`: asks in particular for more efficient
  schedules measured by the number of shifts and for individual nonreal
  central orders from real prime statistics.
* `zer.tex`, proof of `zer:thm:balancing`: continuous convolution powers
  already isolate fixed Fourier coefficients. The finite sample count and
  repeated-alias estimate are absent there.
* `rec.tex`, theorem `rec:thm:quaddecode` and the earlier finite-recovery
  proof: convolutions of uniform interval densities and powers of sinc are
  used in the reverse direction, from a finite zero list to prime data.
* `rec.tex`, theorems `rec:thm:fwidth` and `rec:thm:hblock`: exact minimal
  widths for positive averages annihilating specified frequencies and jets.
  Those constructions use the frequencies being annihilated and do not
  give the finite zero-oblivious grid sample bound proved here.

The three incoming symplectic reports present on the pinned main commit
were inspected to avoid duplicating already delivered work. They cover
arbitrary two-subspace finite-field compression and symplectic-plane
p-adic corners; they have no bearing on the finite-grid analytic theorem.

## Mathematical proof review

The independent review found no gap in the analytic draft supplied at
`research/analytic_extension/grid_projection_theorem.tex`.

The key details checked were:

* The variance calculation gives
  `1-|U_k(i delta)|^2 >= delta^2/(3 pi^2)` for `|delta| <= pi`.
  For the rest of a fundamental alias cell, the sine denominator gives
  `|U_k| <= 1/sqrt(2)`. Both bounds are uniform in `k >= 2`.
* The intervals of radius `theta <= pi` about nonzero aliases have total
  contribution at most
  `2AB/(pi^2 k^2) [zeta(2) log((2+2pi)k) - zeta'(2)]`.
  The central alias contains no nonzero frequency because
  `theta <= eta`. Frequencies on interval boundaries are handled by
  the contraction bound.
* The exponentially decaying analytic remainder contracts by
  `U_k(-a)^m <= ((1+exp(-a))/2)^m`.
* The exact raw-ramp sample count is `(m+1)k+1`, since the finite difference
  adds a shift of one, which is exactly `k` grid steps.
* Every zero of `U_k(w)` lies on `Re(w)=0`; every zero of the finite-
  difference multiplier K lies on `Re(w)=1/2`. Neither can cancel a
  transformed off-critical-line zero in `0 < Re(w) < 1/2`.
* At real poles in that strip, all relevant factors have positive sign,
  so the one-sided Mellin-Landau argument applies.
* For a nonprincipal character, `chi_0 + Re(chi)` is nonnegative on
  integers and has positive spectral weights on `chi_0, chi, conjugate(chi)`.
  The last two have equal central orders. The principal factor has no
  central zero: its finite Euler factors are nonzero and
  `zeta(1/2)=eta(1/2)/(1-sqrt(2))` is nonzero by the positive alternating
  eta series.

## Required limitations

The boxcar cascade is classical; novelty is claimed only for the proved
arithmetic extension and its relation to the supplied article, subject to
the separate literature screen. The count and gap constants need not be
uniform in conductor. A prescribed slower schedule gives eventual
convergence without selecting a gap constant, but not a known finite
stopping threshold. No central nonvanishing theorem or resolution of
Chowla's conjecture follows.

The norm-one noise guarantee is for the normalized statistic d. The
alternative normalized-ramp guarantee has factor B. Unnormalized ramp
roundoff is multiplied by the displayed exponential normalization and
must be budgeted separately.
