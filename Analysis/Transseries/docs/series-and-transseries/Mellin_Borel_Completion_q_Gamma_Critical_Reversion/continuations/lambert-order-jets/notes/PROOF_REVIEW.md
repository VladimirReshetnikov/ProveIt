# Internal proof review

This is an internal review of the delivered arguments, not an independent
referee report or proof-assistant certification.

## Normalizations checked

- Borel transform: `B(t^r)=xi^(r-1)/(r-1)!`, with no `1/t` in the Laplace
  integral. The ordinary tail is normalized by `t^(m-1)`; the first order
  jet is normalized by `t^m`. Confusing these gives a wrong activation factor.
- Actions are `A_N=4*pi^2*N`. With
  `C_m=(-1)^m/(2*pi*i)^(m+1)`, one has
  `4*pi^2*C_m=(i/(2*pi))^(m-1)`.
- Upper-minus-lower Laplace contours are clockwise around the positive
  poles, so the residue multiplier is `-2*pi*i`.
- The double-pole kernel has zero simple residue, but after multiplication
  by `exp(-xi/t)` its residue is `-c_N*exp(-A_N/t)/t`. This yields the
  positive factor `pi*i` in the activation identity.

## Analytic completion is proved separately from the jump

The derivative of the zeta functional equation yields a product expression
`log(2*pi)*G(v)-G'(v)+(pi/2)*tan(pi*v/2)*G(v)`, with
`G(v)=Gamma(v)*zeta(v)`. It avoids division by a possible zeta zero.

Integration by parts on the vertical Mellin contour accounts for the
logarithmically weighted dual correction Xi. The tangent term is evaluated
by the Mellin transform of the simple-pole kernel I. Thus the physical
function is identified independently; residue data alone would not justify
its flat completion.

## Poles and principal values

Ordinary Cauchy principal value is valid for the simple-pole I integral.
It is invalid for a nonzero double-pole Laplace integral, whose symmetric
truncation diverges. The double-pole median is a Hadamard finite part,
implemented by integration by parts on lateral contours. Both descriptions
are explicitly linked in the article and independently tested numerically.

## Order differentiation and collision

The parity epsilon_m is fixed while differentiating in s. The convergent
Mellin integral is differentiated before s is set to m. The collision
formula is computed from Laurent coefficients. Its all-order Stieltjes
cancellation says only that the explicit gamma_r*B(0) term disappears; it
is not a claim that all constants or all logarithms disappear.

## Measures and endpoints

The atomic proof uses distinct points in (0,1), hence distinct nonzero
Fourier nodes. A reflected union has at most 2r points, so the stated finite
certificate follows from an ordinary Vandermonde determinant.

For general finite measures, the one-jet theorem is explicitly a theorem
about integrated polynomial tail-coefficient maps. The exponential moment
generating function is entire because the support is bounded. Eventual
vanishing of all sufficiently high Bernoulli moments makes its Bernoulli
transform a polynomial; evaluation at 2*pi*i*n and Fourier uniqueness
identify the sole blind component as constant Lebesgue measure.

The log-squared endpoint assumption stated in the article suffices for
existence of the integrated physical first jet. It is not used to justify
interchanging the initial right-hand Mellin contour with an arbitrary
measure: that interchange can require negative endpoint moments, a stronger
condition. The polynomial coefficient proof needs no such interchange.

## Reality and domains

The Fourier kernels require real a. Their bounds are uniform for real a,
but generally fail if a is simply made complex. The exact identities extend
in t to Re(t)>0 by normal convergence and analytic continuation, with a
chosen logarithm. Exponential smallness is asserted on closed subsectors,
not on the imaginary-axis boundary.

## Computational scope

The exact run has 732 assertions, including free-variable symbolic
identities and finite cyclotomic computations. The numerical run has 61
assertions, with direct logarithmic weights for the physical order jet and
independent rotated-contour integrations for the sign. The general-measure
infinite theorem is proved in the text, not certified by these finite tests.
No numerical output is described as an interval certificate.
