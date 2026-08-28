# Exponents and q-series

Generalizations of the dyadic construction to arbitrary exponent
sequences and the q-series calculus that organizes them: the
exponent-sequence convolution monoid with its Newton-basis frontiers, and
q-binomial Richardson acceleration of geometric sinc products. The
denominator-free Gaussian/q-binomial core used by both is formalized at arbitrary
ratio. The normalized geometric-Lagrange and analytic Lagrange layers additionally
assume injectivity of `j |-> q^j` on the finite node set (see the status boxes and
crosswalk paragraphs inside the documents). `AnalyticSeriesFilter.lean` carries the core to exact
diagonal and Gaussian-tail identities for unconditionally summable sampled
series. Its hypotheses are sharp at zero-weight nodes, but it does not cover
conditionally convergent boundary series, uniform estimates, signs or bounds,
or the concrete sinc-product/Bell-series instantiation.

The documents also cross-reference the independent real fractional-Volterra
layer. `FractionalVolterraCalculus.lean` proves positive affine covariance on
ordered intervals for arbitrary real order. For `alpha <= 0`, this covariance is
an identity for the totalized Lean interval-integral definition; a classical
Riemann--Liouville/integrability interpretation is asserted only for positive
order. Gamma-normalized order raising holds for real `alpha > 0` from a continuous Banach-valued primitive with an
interval-integrable right derivative. `FabiusFractionalVolterra.lean`
specializes this to the signed Fabius extension for `x >= 0`, the bounded
Fabius function for `0 <= x <= 1`, and the Up-to-Fabius bridge for `x >= -1`.
Complex orders, Caputo/Riemann--Liouville derivatives, weighted-monomial or iterated
shifts, negative-branch and hierarchy formulas, and inverse/quantile versions
remain research frontiers. These API claims were checked at source checkpoint
`22f801337`.

Member: `Exponents_and_q_Series_Frontiers` — the 2026-08-28 consolidation
of the two former drafts (Newton-basis frontiers; q-binomial Richardson),
with their supporting files under `assets/` and provenance recorded in the
document itself.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
