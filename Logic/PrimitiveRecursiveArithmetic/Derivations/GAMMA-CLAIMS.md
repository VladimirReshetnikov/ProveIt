# Gamma source-claim audit

The [Gamma packet](../docs/proofs/analysis/gamma_ipra/) has an explicit
[62-family coverage ledger](../docs/proofs/analysis/gamma_ipra/paper/sections/09_inventory.tex).
That ledger, including its stated domain and order qualifications, is the
source scope. Its entries are families of related results, rather than 62
individual theorem declarations. The entire packet remains unfinished.

Here **checked** means an ordinary `Prf PRAAx` derivation for the actual
finite programs and hypotheses stated by the linked module. Native Lean
lemmas and analytic certificate structures are separate evidence.

## Current checked arithmetic

[GammaEulerMesh](Lean/IPRADerivations/Analysis/GammaEulerMesh.lean)
computes the exact sample `H_N−(H_(KN)−H_K)` on the positive integer
mesh. It proves the C1 difference for a common mesh and the finite
range `[0,1]` on the independently normalized samples.
[GammaEulerConstantName](Lean/IPRADerivations/Analysis/GammaEulerConstantName.lean)
constructs the actual fixed-index and cofinal regular names and proves the
sharp named C1 and C2 comparisons with independent observation errors.
[GammaMeshRobinLogBridge](Lean/IPRADerivations/Analysis/GammaMeshRobinLogBridge.lean)
proves independent-precision agreement of the regular harmonic-mesh and
binary-reduced Robin logarithm names for positive integers. Its Robin
observations use the original numerator and denominator at `p+N+4`. It
also proves that the fixed-index Euler sample plus the logarithm at the
same mesh equals the original exact harmonic value. The unreduced artanh
sampler still needs its own comparison.
[RationalGaussianNameEmbedding](Lean/IPRADerivations/Analysis/RationalGaussianNameEmbedding.lean)
embeds the original regular scalar names as regular Gaussian names,
with exact Euclidean distances and a computed exponential disk.

[GammaCanonicalFactors](Lean/IPRADerivations/Analysis/GammaCanonicalFactors.lean)
implements the finite expression

`−z²/(2N²) + Σ_{j=3}^{L+2} (−1)^(j+1) z^j/(jN^j)`.

Its actual Gaussian-rational numerator and positive denominator have proved
program metadata, disk bounds and finite degree-Cauchy estimates. The input
is an arbitrary signed rational complex `z/B`, with positive runtime `B`.
Both the Taylor degree and the number of summed factors are internal.

For the actual finite sum over indices `N+1,…,N+r`, the module constructs a
positive product denominator and proves the required in-range quotient
clearing. `rational_disk_tail_closed` gives the exact C6 constant `R²/N`
under `N≥1`, `B≥1`, `|z|≤RB` and `2R≤N`. This is a finite, uniform estimate
for the prescribed canonical factors. It does not identify an analytic
logarithm or a Gamma function by its module name.

[GammaCanonicalNames](Lean/IPRADerivations/Analysis/GammaCanonicalNames.lean)
now constructs the actual joint tail name, with factor count
`2^(p+5)(R²+1)` and Taylor length `p+5+count`. A proved overlap comparison
and index-tail estimate each cost at most `2^(-p-5)`. The actual PR5 signed
quotient observations at scale `2^(p+4)` satisfy closed regularity and
ordered-precision bounds, exact program equations, rounding correctness and
the C6 disk bound with only the explicit `2/2^(p+4)` rounding slack.
`primitive_recursive_joint_tail_name` is a name for this prescribed
power-series tail.
[GaussianGammaCanonicalTailName](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTailName.lean)
uses those exact observations as a regular Gaussian rational name with the
C6 radius and the same rounding slack. At the sufficient cutoff `4R²≤N`,
every sample lies in the unit disk, which supplies an actual input and
regular output for the exponential of this tail.
[GaussianGammaCanonicalTailFiniteSplit](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTailFiniteSplit.lean)
identifies the normalized original finite tail with the exact Gaussian sum
of its original factors. One extra factor in the original tail yields
the first factor plus the successor tail at the same Taylor degree.
[GaussianGammaCanonicalTailMetric](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTailMetric.lean)
proves the original same-query comparison with error `8/2^(p+4)`.
[GaussianGammaCanonicalTailShift](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTailShift.lean)
accounts for the retiming of the actual addition and proves the regular
name identity `T_N=L_(N+1)+T_(N+1)` at independent precisions.
[GaussianGammaExactTailDisk](Lean/IPRADerivations/Analysis/GaussianGammaExactTailDisk.lean)
constructs an equivalent regular tail name on the exact C6 disk and
proves its exponential bound when `R²≤N`.
[GaussianGammaCanonicalTailExponential](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTailExponential.lean)
proves that the actual tail exponential approaches one at a computed
cofinal cutoff. The original pure-tail finite sample comparison uses the
C6 radius and the finite three-Lipschitz estimate.
[GaussianGammaEulerHead](Lean/IPRADerivations/Analysis/GaussianGammaEulerHead.lean)
builds the literal finite polynomial in C5 and C7, proves its finite
split and binds each factor to the local C4 constant. At cutoff `2R` its
Euclidean majorant is exactly the polynomial factor in C9.
[GaussianGammaEulerHeadLower](Lean/IPRADerivations/Analysis/GaussianGammaEulerHeadLower.lean)
proves that the original pole guard gives the exact lower bound
`δ^(N+1)/N!` on the literal head. Its actual rational reciprocal
multiplies the head to one and satisfies the corresponding upper bound.
[GaussianBoundedInverseApartness](Lean/IPRADerivations/Analysis/GaussianBoundedInverseApartness.lean)
computes a finite anchor for the original reciprocal-name program from
a bounded regular inverse and proves agreement with that inverse.
[GaussianGammaReciprocalInverse](Lean/IPRADerivations/Analysis/GaussianGammaReciprocalInverse.lean)
constructs the original reciprocal of C7 under the supplied pole guard.
It proves the C13 constant is positive and gives a regular multiplicative
inverse bounded by exactly `1/λ`. The actual Gamma observations obey
`1/λ+2/2^p`.
[GaussianApproximateInverseDistance](Lean/IPRADerivations/Analysis/GaussianApproximateInverseDistance.lean)
and [GaussianNamedInverseRate](Lean/IPRADerivations/Analysis/GaussianNamedInverseRate.lean)
transfer a direct comparison with base rate `D/N` to the exact inverse
rate `A²D/(B²N)` when both inverses have bounds `A/B`.
[GaussianNamedRateTransport](Lean/IPRADerivations/Analysis/GaussianNamedRateTransport.lean)
preserves the exact base rate across replacements by equivalent names.
[GaussianGammaEulerInverseConvergence](Lean/IPRADerivations/Analysis/GaussianGammaEulerInverseConvergence.lean)
instantiates the C15 rate `3M_R(R²+R)/(λ²N)` for the actual Euler
reciprocal and Gamma with independent observation errors.
[GaussianGammaEulerInverseApproximationName](Lean/IPRADerivations/Analysis/GaussianGammaEulerInverseApproximationName.lean)
constructs an actual cofinal sampler from this exact fractional
coefficient and proves that it gives the same regular name as Gamma.
[GaussianGammaRadiusOverlap](Lean/IPRADerivations/Analysis/GaussianGammaRadiusOverlap.lean)
proves agreement of the original C7 and Gamma names at the same
encoded rational point on two supplied disks. Gamma permits separate
pole certificates and actual computed anchors on the two disks.
[GaussianGammaCanonicalExponent](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalExponent.lean)
constructs the actual regular C7 exponent from the Euler constant mesh
name, the exact harmonic value and the original canonical tail at `2R`.
The computed zeroth-observation radius gives a regular exponential.
[GaussianGammaHarmonicIncrement](Lean/IPRADerivations/Analysis/GaussianGammaHarmonicIncrement.lean)
proves the exact scalar and Gaussian identity `H_(N+1)=H_N+1/(N+1)`
for the original harmonic programs.
[GaussianGammaCanonicalExponentBound](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalExponentBound.lean)
proves that every original C7 exponent observation lies in the numerical
disk of radius `2R²+2R`, using the original tail with its rounding error.
[GaussianGammaFixedEulerExponent](Lean/IPRADerivations/Analysis/GaussianGammaFixedEulerExponent.lean)
constructs an exact representative in the same disk for the exponent
built from the fixed Euler observation and both finite-tail summands.
[GaussianGammaFixedEulerExponentBalance](Lean/IPRADerivations/Analysis/GaussianGammaFixedEulerExponentBalance.lean)
proves the addition identity with the original Euler correction.
[GaussianGammaFoldedQBound](Lean/IPRADerivations/Analysis/GaussianGammaFoldedQBound.lean)
then factors the original `Q_N` and gives its exact bounded representative.
[GaussianGammaEulerReciprocalInverse](Lean/IPRADerivations/Analysis/GaussianGammaEulerReciprocalInverse.lean)
constructs its actual reciprocal on the pole-free disk using the same
C13 constant `λ`. The exact representative has bound `1/λ`.
[GaussianRationalLowerPerturbation](Lean/IPRADerivations/Analysis/GaussianRationalLowerPerturbation.lean)
proves the exact Gaussian lower bound near one and the fractional lower
bound for one factor of a product.
[GaussianGammaObservationLower](Lean/IPRADerivations/Analysis/GaussianGammaObservationLower.lean)
uses them to bound the actual `P` and `Q_N` observations below by
`λ max(0,1−K/2^p)` and the Gamma observations below by
`(1/M_R) max(0,1−K/2^p)`. Each `K` is given by the corresponding
original multiplication clock.
[GaussianGammaPoleZeros](Lean/IPRADerivations/Analysis/GaussianGammaPoleZeros.lean)
proves exact zero of the original C7 observations at each encoded
negative integer whose pole index is included in the head.
[GaussianGammaPoleSearch](Lean/IPRADerivations/Analysis/GaussianGammaPoleSearch.lean)
proves the converse for encoded rational inputs. The bounded search
returns an exact pole index or derives separation with `δ=1/B` from
the nonzero translated integer norms. The actual reciprocal anchor
then excludes the original C7 zero predicate in the failure branch.
[GaussianGammaEulerHeadShift](Lean/IPRADerivations/Analysis/GaussianGammaEulerHeadShift.lean)
proves the finite polynomial cancellation underlying C20 for all
numerical cutoffs. Its actual head output satisfies
`z H_N(z+1)=(z+N+1)H_N(z)` by multiplication alone.
[GaussianGammaC7Name](Lean/IPRADerivations/Analysis/GaussianGammaC7Name.lean)
multiplies it by the original polynomial head and gives a regular name
for the displayed C7 expression on each fixed input disk.
[GaussianGammaCutoffName](Lean/IPRADerivations/Analysis/GaussianGammaCutoffName.lean)
verifies the same programs at arbitrary numerical cutoffs satisfying
`N≥1` and `2R≤N`, with literal specialization at `N=2R`.
[GaussianGammaC9Bound](Lean/IPRADerivations/Analysis/GaussianGammaC9Bound.lean)
proves the exact C9 bound `M_R` for every observation of the original
reciprocal name. [GaussianGammaFoldedMajorantExponent](Lean/IPRADerivations/Analysis/GaussianGammaFoldedMajorantExponent.lean)
constructs the same bound for a representative formed from the original
head and the exponent at `2R` minus the tail at `N`.
[GaussianGammaFoldedC9Bound](Lean/IPRADerivations/Analysis/GaussianGammaFoldedC9Bound.lean)
identifies this bounded representative with the original folded finite
`P_N` program. Its original observations obey `M_R+2/2^p`.
[GaussianGammaFiniteApproximantName](Lean/IPRADerivations/Analysis/GaussianGammaFiniteApproximantName.lean)
constructs the folded C5 names from the original polynomial head,
Euler constant, harmonic value, and harmonic-mesh logarithm. It proves the
actual sampling equations and regularity.
[GaussianGammaWeierstrassFactors](Lean/IPRADerivations/Analysis/GaussianGammaWeierstrassFactors.lean)
checks the literal finite products at a common Taylor cutoff.
[GaussianGammaWeierstrassFiniteName](Lean/IPRADerivations/Analysis/GaussianGammaWeierstrassFiniteName.lean)
normalizes the actual factor fold and compares it to the negative
harmonic exponential.
[GaussianGammaWeierstrassApproximant](Lean/IPRADerivations/Analysis/GaussianGammaWeierstrassApproximant.lean)
attaches the original Euler-constant exponential and identifies the
literal factor-by-factor name with the original folded `P_N`.
[GaussianGammaWeierstrassConvergence](Lean/IPRADerivations/Analysis/GaussianGammaWeierstrassConvergence.lean)
proves that the folded name approaches C7 at rate `3M_R R²/N`.
[GaussianGammaWeierstrassLimit](Lean/IPRADerivations/Analysis/GaussianGammaWeierstrassLimit.lean)
transfers the exact rate to the literal factor program and evaluates
it at a computed cofinal cutoff. The resulting actual regular sampler
agrees with the original C7 reciprocal at independent precisions.
[GaussianGammaLogHarmonicName](Lean/IPRADerivations/Analysis/GaussianGammaLogHarmonicName.lean)
proves that the actual sum of the fixed-index Euler and harmonic-mesh
logarithm names agrees with the exact harmonic constant at independent
precisions.
[GaussianGammaExponentStep](Lean/IPRADerivations/Analysis/GaussianGammaExponentStep.lean)
proves the actual exponent identity for adjacent cutoffs by combining
the harmonic increment, tail shift and original local full logarithm.
[GaussianGammaAdjacentCutoff](Lean/IPRADerivations/Analysis/GaussianGammaAdjacentCutoff.lean)
uses local C4 and the literal head successor to prove agreement of the
complete C7 names at adjacent cutoffs, including zeros of the polynomial
head. [GaussianGammaFoldedApproximantBalance](Lean/IPRADerivations/Analysis/GaussianGammaFoldedApproximantBalance.lean)
proves both C8 product identities for the actual folded programs.
[GaussianGammaCutoffIndependence](Lean/IPRADerivations/Analysis/GaussianGammaCutoffIndependence.lean)
uses quantifier-free induction at fixed observation precision, followed
by an envelope comparison, to derive agreement at any two valid
numerical cutoffs. [GaussianGammaEulerCorrectionDisk](Lean/IPRADerivations/Analysis/GaussianGammaEulerCorrectionDisk.lean)
proves the exact `R/N` disk for the represented Euler correction.
[GaussianGammaPerturbationExponent](Lean/IPRADerivations/Analysis/GaussianGammaPerturbationExponent.lean)
proves the actual difference-of-exponents envelope at `(R²+R)/N`
and its relation to the original correction.
[GaussianGammaEulerConvergence](Lean/IPRADerivations/Analysis/GaussianGammaEulerConvergence.lean)
combines the two C8 product identities by multiplication and proves the
C10 bound `3M_R(R²+R)/N` with the two ordinary independent observation
errors. [GaussianGammaEulerApproximationName](Lean/IPRADerivations/Analysis/GaussianGammaEulerApproximationName.lean)
chooses a numerical cutoff and one additional observation bit to
construct an actual regular cofinal Euler sampler equivalent to the
original reciprocal name.

[GammaCanonicalRemainder](Lean/IPRADerivations/Analysis/GammaCanonicalRemainder.lean)
proves the sharp finite C3 remainder between cutoffs `L` and `L+K` of the
actual factor at the same rational argument. The cleared scale is
`(L+3)N^(L+2)(N-R)`, and the right-hand radius power is `R^(L+3)`.
The returned PR5 data retain both original positive denominators and the
certificate proves the positivity of this scale under `R<N`.

[GammaLocalFactorName](Lean/IPRADerivations/Analysis/GammaLocalFactorName.lean)
constructs the actual local-factor name on `N≥1`, `|z|≤R` and `2R≤N`.
It gives a PR4 signed dyadic observation at scale `2^(p+4)`, proves
regularity at independent precisions, and gives the disk bound
`R²/N² + 2/2^(p+4)`. The sharp finite C3 bound also compares an original
fixed cutoff with a cofinal name observation, with explicit rounding
slack. The original logarithm and its exponential are identified below.

The reusable [ReciprocalSquareTail](Lean/IPRADerivations/Analysis/ReciprocalSquareTail.lean)
provides the underlying uniform rational inverse-square comparison.
The [complex logarithm modules](Lean/IPRADerivations/Analysis/ComplexLogarithmName.lean)
construct a different canonical local power-series name and its exact
rounding/Cauchy bounds; they do not automatically instantiate Gamma's Euler
approximants, elementary function error budgets, or branch/domain contracts.

[LogarithmExponentialCoefficients](Lean/IPRADerivations/Analysis/LogarithmExponentialCoefficients.lean)
now proves a finite algebraic dependency of C4. Its actual signed Bell/history
program uses the proved kernel `g_k=(-1)^k k!`, and derives the differential
coefficient recurrence, initial values and zero coefficients at every
internal degree at least two. The rational coefficients use proved-positive
factorials. The low coefficients of the literal finite sum of powers of the
truncated logarithm are identified below. Transport to the actual analytic
exponential and logarithm names requires their tail bounds.

[FiniteExponential](Lean/IPRADerivations/Analysis/FiniteExponential.lean)
and [FiniteLogarithm](Lean/IPRADerivations/Analysis/FiniteLogarithm.lean)
now evaluate the literal factorial-cleared finite sums, together with
independent termwise derivative sums. Exact coefficient clearing identifies
the prescribed `1/k!` and alternating `1/j` coefficients. Internal-cutoff
QF inductions derive their evaluation recurrences and exact differential
residuals `D E'_N+x^N=E_N` and
`(D+x)H'_N+g_N x^N=N!D^N`. Positive-denominator and actual PR3 output
contracts are checked. The complex composition, coefficient bounds, tails,
and original logarithm name identity follow in the modules below.

[GaussianRationalPolynomialPowers](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialPowers.lean)
provides the stored Gaussian-rational power buffers needed for the literal
finite composition. With the original coefficient length, the computed
buffer evaluates to the corresponding power of the original Horner value.
Every in-range successor also has the actual convolution coefficient law.
[GaussianRationalPolynomialExponential](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialExponential.lean)
constructs the actual factorial-weighted coefficient sum. Its Horner
evaluation is the literal finite complex exponential sum of the original
value.

[GaussianFiniteLogarithmPolynomial](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmPolynomial.lean)
constructs the original truncated logarithm polynomial and identifies each
stored coefficient with the original factorial kernel. Its actual finite
exponential composition has the literal finite complex Horner value.
[GaussianIntegerFractionPowers](Lean/IPRADerivations/Analysis/GaussianIntegerFractionPowers.lean)
proves the exact fraction powers and signed factorial numerator.
[GaussianFiniteLogarithmSampler](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmSampler.lean)
identifies the value of the same logarithm polynomial with the original
cleared numerator and denominator.
[GammaLogarithmFactorBridge](Lean/IPRADerivations/Analysis/GammaLogarithmFactorBridge.lean)
identifies that sample with the sum of the original linear term and
the original canonical factor and evaluates the actual finite exponential
composition at that argument. The low-degree coefficients and analytic tail
are checked below.
[GaussianRationalLowCoefficientConvolution](Lean/IPRADerivations/Analysis/GaussianRationalLowCoefficientConvolution.lean)
identifies low coefficients of the actual stored polynomial product with
their finite ascending Cauchy sums.
[GaussianRationalPolynomialPowerSupport](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialPowerSupport.lean)
uses that identity to derive the zero coefficients below the original
power exponent.
[GaussianRationalPolynomialExponentialStability](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialExponentialStability.lean)
proves that the actual low coefficient of the original composition is
already attained at the stage indexed by that coefficient. The remaining
coefficient comparison is with the Bell recurrence.
[GaussianRationalPolynomialExponentialCoefficients](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialExponentialCoefficients.lean)
identifies the same coefficient with the exact inverse-factorial-weighted
sum of stored power coefficients.
[GaussianRationalWeightedCoefficientConvolution](Lean/IPRADerivations/Analysis/GaussianRationalWeightedCoefficientConvolution.lean)
derives the exponent-weighted product rule on those same low coefficients.
[GaussianRationalEulerCoefficients](Lean/IPRADerivations/Analysis/GaussianRationalEulerCoefficients.lean)
stores the actual exponent-weighted coefficients, implements the product rule
with the actual output buffers, and derives the alternating unit Euler
coefficients of the original logarithm.
[GaussianRationalPolynomialPowerEuler](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialPowerEuler.lean)
derives the exact Euler rule for the low coefficients of the original stored
powers, including the source logarithm.
[GaussianRationalFactorialEulerSums](Lean/IPRADerivations/Analysis/GaussianRationalFactorialEulerSums.lean)
shifts the exact factorial-weighted sum after applying that rule to the
original composition.
[GaussianRationalExponentialProductCoefficients](Lean/IPRADerivations/Analysis/GaussianRationalExponentialProductCoefficients.lean)
identifies the shifted finite sum with the actual product of the Euler-weighted
base and the accumulated exponential.
[GaussianRationalFiniteExponentialEuler](Lean/IPRADerivations/Analysis/GaussianRationalFiniteExponentialEuler.lean)
combines power support with the exact cutoff to derive the finite exponential
Euler rule for the original logarithm at every exponent within both cutoffs.
[GaussianRationalCoefficientRecursion](Lean/IPRADerivations/Analysis/GaussianRationalCoefficientRecursion.lean)
proves bounded uniqueness for an actual prior-coefficient recursion.
[GaussianFiniteLogarithmCoefficientRecursion](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmCoefficientRecursion.lean)
derives that recursion and its initial value on the original stored
composition.
[GaussianFiniteLogarithmLinearRecursion](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmLinearRecursion.lean)
verifies the same recurrence on the actual two-coefficient linear buffer.
[GaussianFiniteLogarithmBellIdentification](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmBellIdentification.lean)
then identifies the coefficients of the literal finite composition with the
original signed Bell values at each exponent within both internal cutoffs.
[GaussianFiniteLogarithmCompositionTail](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmCompositionTail.lean)
derives the actual residual from the stored high coefficients and bounds its
size on the source half-disk using the computed stage coefficient budget.
A uniform weighted majorant remains necessary for the analytic modulus.
[GaussianRationalPolynomialDilation](Lean/IPRADerivations/Analysis/GaussianRationalPolynomialDilation.lean)
constructs the actual scaled-argument buffer and proves the weighted
coefficient arithmetic used to produce that majorant.
[GaussianFiniteLogarithmWeightedNorm](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmWeightedNorm.lean)
bounds the actual truncated logarithm at auxiliary weight 5/9 by 65/72
for every original truncation degree.
[GaussianFiniteExponentialWeightedNorm](Lean/IPRADerivations/Analysis/GaussianFiniteExponentialWeightedNorm.lean)
then bounds the weighted norm of the original finite exponential composition
by 72/7 at the same auxiliary weight. Convergence at the source disk still
requires the tail and truncation comparisons.
[GaussianRationalUnitDiskHornerNorm](Lean/IPRADerivations/Analysis/GaussianRationalUnitDiskHornerNorm.lean)
uses the original Horner size bound to control each prefix of the same
dilated composition by 11 at the rescaled source argument of radius at most
9/10.
[GaussianFiniteLogarithmGeometricTail](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmGeometricTail.lean)
identifies the actual high-prefix residual after subtracting the linear part
and bounds it on the original half-disk by the geometric tail. The passage
to a dyadic error bound is checked by
[GaussianFiniteLogarithmDyadicTail](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmDyadicTail.lean).
[GaussianFiniteLogarithmCompositionName](Lean/IPRADerivations/Analysis/GaussianFiniteLogarithmCompositionName.lean)
constructs the regular cofinal name from the original finite Gamma-factor
samples and proves its equivalence to the constant name `1+w`.
[GaussianRationalExponentialTail](Lean/IPRADerivations/Analysis/GaussianRationalExponentialTail.lean)
proves the original scalar-sum cutoff comparison on a bounded Gaussian
rational input. [GaussianRationalExponentialName](Lean/IPRADerivations/Analysis/GaussianRationalExponentialName.lean)
constructs the original cutoff name at such queries.
[GaussianRationalExponentialLipschitz](Lean/IPRADerivations/Analysis/GaussianRationalExponentialLipschitz.lean)
proves the uniform three-Lipschitz estimate for the original finite
scalar exponential on the unit disk.
[GaussianRationalRadiusExponentialLipschitz](Lean/IPRADerivations/Analysis/GaussianRationalRadiusExponentialLipschitz.lean)
proves the cutoff-dependent Lipschitz estimate on any numerical disk
and bounds it by the computed binary precision factor.
[GaussianRadiusExponentialName](Lean/IPRADerivations/Analysis/GaussianRadiusExponentialName.lean)
uses that factor to compute the sampling clock for an actual regular
exponential on any fixed numerical disk. The exponential preserves
independent-precision equivalence of input names on that disk.
[GaussianScalarExponentialDiagonal](Lean/IPRADerivations/Analysis/GaussianScalarExponentialDiagonal.lean)
proves that the actual triangular Cauchy sum is exactly the original
finite scalar exponential of the sum.
[GaussianScalarExponentialProductLowDegrees](Lean/IPRADerivations/Analysis/GaussianScalarExponentialProductLowDegrees.lean)
binds the original rectangular product and identifies its exact difference
with the sum of its actual high-degree coefficients.
[GaussianScalarExponentialProductTail](Lean/IPRADerivations/Analysis/GaussianScalarExponentialProductTail.lean)
proves the requested dyadic error of that actual high part at a computed
cutoff. [GaussianExponentialReference](Lean/IPRADerivations/Analysis/GaussianExponentialReference.lean)
compares each actual observation with the original finite sum at a common
later input and cutoff. [GaussianExponentialAddition](Lean/IPRADerivations/Analysis/GaussianExponentialAddition.lean)
uses the original addition and multiplication clocks to prove
`exp(u+v)=exp(u)exp(v)` at independent observation precisions on a common
numerical disk with `R≥1`.
[GaussianExponentialRadiusIndependence](Lean/IPRADerivations/Analysis/GaussianExponentialRadiusIndependence.lean)
proves exponential properness with independent input disks and agreement
with the actual specialized unit-disk exponential.
[GaussianExponentialInverse](Lean/IPRADerivations/Analysis/GaussianExponentialInverse.lean)
proves that multiplying the exponential of the original name by the
exponential of its actual negative gives the constant one.
[GaussianExponentialDiskMajorant](Lean/IPRADerivations/Analysis/GaussianExponentialDiskMajorant.lean)
transfers the actual finite series on the nonnegative real axis to a
Euclidean bound throughout the disk.
[GaussianPositiveExponentialProduct](Lean/IPRADerivations/Analysis/GaussianPositiveExponentialProduct.lean)
proves positivity of the original high-degree part and submultiplicativity
of the real finite sums.
[GaussianPositiveExponentialMajorant](Lean/IPRADerivations/Analysis/GaussianPositiveExponentialMajorant.lean)
uses those positive sums and the unit factorial bound to prove `3^R`
for the original finite exponential on the entire numerical disk at
every cutoff.
[GaussianUnitDiskExponentialName](Lean/IPRADerivations/Analysis/GaussianUnitDiskExponentialName.lean)
uses the actual scalar sums to construct a regular exponential of an
argument name with unit-disk samples and proves preservation of name
equivalence.
[GaussianExponentialSmallPerturbation](Lean/IPRADerivations/Analysis/GaussianExponentialSmallPerturbation.lean)
proves the finite and named bound `3A/B` from one under a disk bound
`A/B≤1`. The product estimate for a bounded prefactor is `3MA/B`,
including at zeros. [GaussianExactDiskShrinking](Lean/IPRADerivations/Analysis/GaussianExactDiskShrinking.lean)
constructs an equivalent name with exact disk radius from a bound with
dyadic observation slack. [GaussianExactDiskExponential](Lean/IPRADerivations/Analysis/GaussianExactDiskExponential.lean)
transports this correction through the actual exponential programs.
[GaussianNamedSmallPerturbationTransport](Lean/IPRADerivations/Analysis/GaussianNamedSmallPerturbationTransport.lean)
proves the prefactor estimate at independent precisions using the
actual original multiplication clock.
[GaussianLocalLogarithmName](Lean/IPRADerivations/Analysis/GaussianLocalLogarithmName.lean)
proves regularity and the unit-disk bound on every original unshifted
logarithm observation.
[GaussianLocalLogarithmExponentialIdentity](Lean/IPRADerivations/Analysis/GaussianLocalLogarithmExponentialIdentity.lean)
then compares the actual exponential of that name with the constant name
`1+z/N` in both the cross and diagonal relations on the original half-disk
with `N≥1`. It also proves equivalence with the actual cofinal finite
composition. These are object-theory derivations of the local C4 identity.

## Every ledger family remains in scope

| Ledger IDs | Complete source deliverables still required |
| --- | --- |
| 1 | Actual harmonic/logarithm Euler-constant evaluator, C1–C2 inequalities, a regular name, and its bounds. |
| 2–3 | Actual cofinal samplers establish C11 for the literal Weierstrass product and C15 for the Euler reciprocals. The C7 and Gamma names agree on overlapping disks for the same encoded rational point. Agreement with the right half-plane integral construction remains. |
| 4–10 | The original C7 zero predicate is characterized by an exact pole search for encoded rational inputs. The actual Gamma observations have a quantitative nonvanishing bound on pole-free disks. The coefficient majorants, entire analyticity, zero classification for general named inputs, simplicity of the zeros, poles and residues, functional equation and normalization, factorial values, conjugation and real-domain values remain. |
| 11–17 | Actual quadrature and both endpoint tails, Euler-integral identification, quantitative positive lower/upper bounds, vertical absolute-value comparison, fixed-order derivative integrals, substitution/scaling formulas, and incomplete-Gamma sum/recurrence/integer formulas. |
| 18–24 | Reflection with an explicit sine margin, multiplication at arbitrary internal positive integer multiplier, duplication/triplication, beta–Gamma relation, beta symmetry/recurrence and all stated integral forms with their positive half-plane margins. |
| 25–30 | Positive-root selection and half-integer values, the listed fractional-argument relations and fractional products, rising/binomial cancellation through apparent poles, and imaginary/half-shifted modulus formulas, including their zero-safe versions. |
| 31–36 | Digamma and polygamma evaluators with remainder bounds, recurrences/signs/special derivative values, differentiated reflection/multiplication, rational-argument values, and the finite polynomial recursion for Gamma derivatives. Derivative orders may remain external where the source explicitly allows that schema. |
| 37–42 | Quantified local Taylor/log-Gamma expansions, entire reciprocal coefficient recursion, Laurent constants/remainders at each pole, positive-integer-centered expansions, vertical modulus products and balanced parameter products. Coefficient programs and discarded-tail estimates must be connected to the same named functions. |
| 43–48 | Quantitative strict convexity, effective Bohr–Mollerup uniqueness at fixed presentations, Wendel/Gautschi inequalities, rate-bearing Gamma ratios, actual positive-minimum location and negative-pole interval extremum/sign constructions. |
| 49–53 | Leading Stirling/relative errors, Robbins bounds, every fixed order of log-Stirling and digamma expansions with the signed positive-real-axis remainder, and the actual multiplicative-coefficient/error algorithm. Generic Euler–Maclaurin components need application-specific endpoint and positivity proofs. |
| 54–58 | Branch-specified analytic log-Gamma on the certified right half-plane, both Binet formulas and their finite kernel/tail bounds, complete monotonicity, Raabe/unit-interval log-Gamma integrals and the Gamma–zeta Mellin identity for `Re(s)>1`. |
| 59–62 | Wallis product with a rational rate, Gaussian moments and Gamma-density normalization/moments, both Gamma-crossing equations with the golden-ratio solution, and the stated alternative factorial interpolations. |

In particular, a finite factor bound or a generic exponentiation/logarithm
interface does not prove a source assertion identifying the completed named
function. A supplied final approximation certificate would be a conditional
consumer; constructing that certificate for the actual evaluator remains
part of the task.

## Source artifacts and representation boundaries

The delivered [Lean companion](../docs/proofs/analysis/gamma_ipra/lean/README.md)
reports fourteen native finite arithmetic lemmas, executable rational
approximants and uninstantiated analytic certificate structures.
Its [GammaIPRA.lean](../docs/proofs/analysis/gamma_ipra/lean/GammaIPRA.lean)
uses host `Nat`, `Rat` and host function names. Those native results are not
ordinary iPRA derivations, and a definition of `EulerErrorCertificate` is not
a constructed certificate for the Euler evaluator. Historical audit and
executable example receipts retain their stated, narrower meaning.

Numerical inputs, finite lengths, radii, precision and separation data must
be internal where the source is uniform in them. PR evaluators and any
explicitly permitted derivative/asymptotic-order schemas can be fixed before
proof generation. Positive lower bounds authorize inversion; a bare negated
equality of arbitrary represented complex names does not supply them.

The source explicitly excludes its listed deep arithmetic assertions,
Hankel contours, complex-sector full Stirling remainders and specific software
performance/decimal-table claims. Those exclusions are preserved rather
than turned into new completion requirements. The 62 included families and
the finite-precision interfaces remain the target.

See [PROGRESS.md](PROGRESS.md) for the full repository packet scope.
