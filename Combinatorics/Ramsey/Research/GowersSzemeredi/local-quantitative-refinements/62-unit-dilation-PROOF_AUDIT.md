# Proof audit and exact-check scope

This audit records checks performed during manuscript development. It is not
an independent review and does not imply formal verification.

## Critical interfaces

**Integer versus modular dependence.** The proportional coefficient vectors
are the *integer* multiples of the balanced sign vector. Modular dependence
among other vectors is not discarded. It is counted exactly through
`N^(m-2) gcd(N,d_1,...,d_(m-1))`. This is essential over composite moduli.

**Units, not arbitrary scalars.** If a defect has order q, reduction from the
units modulo M to units modulo q is surjective. Uniform unit dilation tests
primitive q-th roots even when q is small. Arbitrary scalar averaging instead
has an asymptotic good/bad enhancement ratio q at a fixed defect order.

**Kernel positivity.** `P_(m,L)` is an m-fold convolution of the nonnegative
function `L F_L`. The sampling proof uses positivity of the entire kernel.
It never assumes that each Ramanujan sum or individual Fourier contribution
is nonnegative.

**Signed arithmetic error.** Each nonproportional coefficient contribution
has absolute target average at most one. Summing its nonnegative coefficient
weight before estimating the number of domain solutions yields the exact
weighted gcd constant. Both the good and bad families obey that bound.

**Removal of the constant-vector event.** In the gcd formula, all-equal
transformed coefficient vectors are excluded. Their probability is the main
coefficient `A/L^m`, and counting them again in the error would destroy the
uniform bound. The residue formula subtracts this event for every divisor.

**Finite versus limiting constant.** The formula for kappa-star has a
zeta-ratio limit, but the value at L=3 and m=16 is strictly greater than that
limit. All finite theorems use the proved rational envelope K_m, not the
limiting value. The verifier checks the finite overshoot using rationals.

**Repeated vertices.** A position-by-position Fourier product is not the
survival probability when a point occurs more than once. The proof keeps
these two quantities separate. Repeated points help the lower bound for
respected tuples. The upper bound for bad tuples adds at most
`binomial(m,2) N^(m-2)`. The count uses another coefficient equal to +1 or -1,
which is available because m>=4. No inverse of 2 modulo N is required.

**One simultaneous selection.** The objective is
`eta*G - (1-eta)*Y = eta*(G+Y)-Y`. A realization with sufficiently large
positive objective simultaneously gives the quality ratio and an absolute
lower bound on G. The proof does not select good count and bad count on
different outcomes.

**Constant accounting.** The filter choice implies `alpha*eta*A >= 4H`.
The size threshold bounds the arithmetic and repetition loss by at most a
quarter of the enhanced good term. The remaining half yields
`alpha/((m+1)L^(m-1))`. At m=16, `K16<2`, `C16=120`, and
`2*17*(2+120)=4148`. The coarser bound `L<2^16 (alpha eta)^(-2)` produces
the displayed constants `2^253` and `2^(-245)`.

**Labelled extension.** A base point has at most R labels. The tuple cap is
`R |X|^(m-1)`, not `|X|^(m-1)`. General arithmetic errors have R^m lifts,
while an equality of two labels has at most R^(m-1) lifts. This yields the
rounding coefficient C_m/R after normalization.

**Scope of sharpness.** The primorial construction proves that this specific
unit-Fejer primitive response has unbounded double-logarithmic worst-case
size. It does not prove that all restriction methods require that loss, nor
that the powers of the density and accuracy parameters are optimal.

## Executed exact checks

All assertions in `code/verify.py` use integer arithmetic or
`fractions.Fraction`. Floating-point numbers are only used for displayed
decimals and logarithms. The standard-library verifier performs:

- 19,716 primitive-response checks over m=4,6,8,16, L=2..32, q=2..160;
- 2,184 weighted-modulus cases, and 22 independent coefficient enumerations;
- all subset outcomes in six small group examples (312 outcomes in total);
- 28 dyadic and coarse-parameter cases, the small-L identities, the exact
  finite overshoot, four primorial cases, and an order-two regression table.

The subset tests compute rational joint probabilities by finite Fourier
convolution, recover the full subset distribution by Mobius inversion, and
check that its probabilities are nonnegative and sum to one. Direct tuple
counts then check the weighted-error and repeated-vertex inequalities.

These finite examples are deliberately small enough to enumerate exactly.
They are not evidence that the huge sufficient size threshold is necessary,
and are not an empirical substitute for the universal argument. The general
labelled-domain extension and asymptotic limits are proved in prose, not
exhaustively certified by the finite test suite.

## Corrections during audit

The initially stated number of subset outcomes was corrected from 336 to
312, matching `8+16+32+64+64+128` and the recorded test output. The labelled
extension now states its parameter ranges explicitly. No independent review,
Lean compilation, global Ramsey bound, or publication-priority result is
claimed.
