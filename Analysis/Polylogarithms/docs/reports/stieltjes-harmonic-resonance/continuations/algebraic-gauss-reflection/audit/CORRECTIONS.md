# Corrections and normalization hazards

## Actual version-specific correction

**Source:** Can, Kargın, Cenkci, Dil, *On certain harmonic zeta functions*,
arXiv:2403.07123 **version 1**, PDF page 1, bottom unnumbered display.
Both the HTML and the actual PDF page were inspected.

The printed Stieltjes-limit formula sums from `n=1`, while its preceding
Hurwitz definition and Laurent normalization use `n=0`. For real `a>0`
the correct lower index is `n=0`:

    gamma_m(a) = lim_N [ sum_{n=0}^N log(n+a)^m/(n+a)
                        - log(N+a)^(m+1)/(m+1) ].

Alternatively, retain `n=1` and add `log(a)^m/a`.
The printed limit is gamma_m(a+1), because

    gamma_m(a+1) = gamma_m(a) - log(a)^m/a.

At m=0, a=1 it is `lim_N(H_(N+1)-1-log(N+1)) = gamma-1`, not gamma.
This is a local off-by-one error, not a finding about the paper's other
results. No assertion is made about later revisions.

Source PDF: https://arxiv.org/pdf/2403.07123v1

## Corrections to tempting extensions, not errors attributed to the repository

1. A reflection of complex-order harmonic data is `a -> 1+u-a`, not
   `a -> 1-a`. The frozen depth-one symmetric combination has value 1
   at s=0, whereas the correctly moving combination has value 0.
2. Normal spectral derivatives cannot be obtained from a formula known
   only on s=-r. For example,
   A_1(1,1,-1+epsilon;c) = (c-1/2) epsilon - epsilon^2/2.
3. Finite parts of varying products require residue terms. This is why
   the depth-two reflected finite-part identity has an extra zeta/2.
4. The local remainder in the negative-Laurent theorem begins at the
   first positive spectral coefficient; it cannot be discarded for
   derivatives or higher harmonic Stieltjes coefficients.

No contradiction to the cited accepted Gauss subtraction or fixed-shift
Laurent theorem was found in the targeted audit. The negative-integer
finite-part formula was recognized as prior work and is not relabeled
as new here.
