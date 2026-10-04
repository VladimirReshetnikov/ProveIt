# Internal proof and scope review

4 October 2026. This is an internal consistency review, not an independent
referee report, Lean certificate, or priority assessment.

## 1. What is reconstructed

The formal logarithm is E(a,h) - Phi_hat(a,h). The exact product is not
identified with an unspecified Borel sum. The two lateral sums differ from
it by different convergent dual logarithms. Their average misses the even
combination of these logarithms. This even combination cannot be recovered
from the Stokes jump alone.

The Mellin proof establishes that missing even part directly. It does not
infer the exact function solely from residues or asymptotic coefficients.
The logarithms of dual products have zero constant term, so their branches
are fixed before comparison with the original paper's notation.

## 2. Mellin strip and principal value

The original Mellin contour lies to the right of 1. It is shifted to a line
with -2 < Re(s) < -1; the three crossed poles give exactly E. The transformed
contour has 1 < Re(u) < 2, where all Dirichlet series and vertical integrals
used in the functional-equation splitting converge absolutely.

The symmetric kernel K has a Mellin transform throughout 0 < Re(u) < 2.
The proof first deletes a symmetric interval around its pole. Subtracting
the pole numerator at the pole bounds the deletion error by an integrable
multiple of delta*(1+T)*exp(-T/2). This justifies exchanging the principal-value
limit with Mellin integration. The separate sine and cosine contributions
then identify the median and the flat completion.

## 3. Borel kernel and complex parameters

The sine Fourier expansion is used only for real 0<a<1. In general it diverges
for nonreal a, and is not used for parameter differentiation there. Instead,
the Bernoulli generating function gives a meromorphic Borel kernel entire
in a. Normal convergence on compact sets and local exponential bounds justify
small-h complex-parameter continuation. The exact factorial recurrence
extends the calculation to neighborhoods of other positive real parameters.

All claims remain local near positive parameters when h is complex. They do
not supply uniform estimates as the gamma parameter approaches a pole.

## 4. Signs and the conjecture comparison

The convention is Borel(h^n) = xi^(n-1)/(n-1)!, with a Laplace integral having
no extra factor 1/h. The upper-minus-lower contour is clockwise. Its residue
factor is therefore -2*pi*i, not +2*pi*i.

The positive pole residue of the elementary pole pair is -1/2. The resulting
upper lateral integral is K + (pi*i/2)*exp(-A0/h). Consequently:

- S_plus(Phi_hat) - S_minus(Phi_hat) = L_minus - L_plus;
- S_plus(p_hat) = p - L_minus;
- S_minus(p_hat) = p - L_plus.

The rotation h=-2*pi*i*N*y sends the positive real y-Borel ray to the lower
half of the h-Borel plane. This swaps the apparent lateral labels in the
translation to Fantini–Rella. The dual index-zero product factor is explicitly
removed. The excluded residue class k=0 is not inserted into a singular
logarithm.

The weighted criterion follows from coefficientwise Möbius inversion and the
invertibility of the finite Fourier transform. Oddness, not primitivity, is
the relevant condition for Dirichlet-character reconstruction. This does not
settle other modular-resurgence conjectures in the cited paper.

## 5. Regular and critical inversion

The all-order regular response is an analytic Lagrange formula. Summability
compatibility is asserted only in classes where the necessary closure and
realization hypotheses hold. A normally summable countable perturbation result
is provided, not a theorem for arbitrary accumulated-action supports.

At an order-r critical point, the substitution x=c+s*u, t=s^r removes the
singular balance. The normalized roots must be nonzero and separated; target
patches meeting the scaled discriminant are excluded. Joint holomorphy,
uniform radii, and a nondegenerate normalized leading coefficient are explicit
hypotheses. The implicit-function theorem then yields convergent expansions
in s, with Cauchy remainder bounds.

The separate moving-fold theorem supplies the square-root chart through the
actual moving branch point. A common vanishing factor changes the effective
critical order and hence the action division. The manuscript does not apply
-linear jump divided by derivative- uniformly at a fold.

## 6. q-gamma examples

The original q-gamma function, the lateral sums, and the median-forward
function have different critical centers and values. These distinctions are
retained in the target equations. The h-dependent coefficient blocks are
kept intact: replacing a moving coefficient by its limiting constant would
generally spoil an O(Q) remainder after a square-root displacement.

The reflected product cancels the entire Bernoulli tail and has no Stokes
jump. Its exact flat correction is nevertheless nonzero. Its inverse is
constructed first as a convergent lift in independent h and Q, and only then
restricted to Q=exp(-4*pi^2/h). Evenness about a=1/2 explains the odd powers of
sqrt(Q) in its root displacement.

The h-inverse has a separate normalization. The ratio of the dual action
4*pi^2 to the dominant action pi^2/6 is 24. Its first correction sign is checked
against the exact logarithmic equation, and cancellation of the first action
at a=1/4 or 3/4 is accounted for.

## 7. Verification boundary

All 144 symbolic assertions passed. They check finite algebraic identities,
coefficient formulas, divisor inversion examples, and rational inequalities.
High-precision tests independently compare the physical product with an
accelerated Borel-kernel calculation and solve critical inverse equations.
They are not interval certificates. Neither test suite proves an infinite
analytic theorem or establishes novelty.

The final LaTeX build is clean. Rendered pages were inspected; the table of
contents, principal proof formulas, critical inverse formulas, and the
proof-dependency table have no observed clipping or overlap.
