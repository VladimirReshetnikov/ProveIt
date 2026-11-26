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

[GammaEulerMesh](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GammaEulerMesh.lean)
computes the exact sample `H_N−(H_(KN)−H_K)` on the positive integer
mesh. It proves the C1 difference for a common mesh and the finite
range `[0,1]` on the independently normalized samples.
[GammaEulerConstantName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GammaEulerConstantName.lean)
constructs the actual fixed-index and cofinal regular names and proves the
sharp named C1 and C2 comparisons with independent observation errors.
[GammaMeshRobinLogBridge](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GammaMeshRobinLogBridge.lean)
proves independent-precision agreement of the regular harmonic-mesh and
binary-reduced Robin logarithm names for positive integers. Its Robin
observations use the original numerator and denominator at `p+N+4`. It
also proves that the fixed-index Euler sample plus the logarithm at the
same mesh equals the original exact harmonic value. The unreduced artanh
sampler still needs its own comparison.
[RationalGaussianNameEmbedding](Lean/IPRADerivations/Analysis/Names/RationalGaussianNameEmbedding.lean)
embeds the original regular scalar names as regular Gaussian names,
with exact Euclidean distances and a computed exponential disk.

[GammaCanonicalFactors](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GammaCanonicalFactors.lean)
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

[GammaCanonicalNames](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GammaCanonicalNames.lean)
now constructs the actual joint tail name, with factor count
`2^(p+5)(R²+1)` and Taylor length `p+5+count`. A proved overlap comparison
and index-tail estimate each cost at most `2^(-p-5)`. The actual PR5 signed
quotient observations at scale `2^(p+4)` satisfy closed regularity and
ordered-precision bounds, exact program equations, rounding correctness and
the C6 disk bound with only the explicit `2/2^(p+4)` rounding slack.
`primitive_recursive_joint_tail_name` is a name for this prescribed
power-series tail.
[GaussianGammaCanonicalTailName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTailName.lean)
uses those exact observations as a regular Gaussian rational name with the
C6 radius and the same rounding slack. At the sufficient cutoff `4R²≤N`,
every sample lies in the unit disk, which supplies an actual input and
regular output for the exponential of this tail.
[GaussianGammaCanonicalTailFiniteSplit](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTailFiniteSplit.lean)
identifies the normalized original finite tail with the exact Gaussian sum
of its original factors. One extra factor in the original tail yields
the first factor plus the successor tail at the same Taylor degree.
[GaussianGammaCanonicalTailMetric](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTailMetric.lean)
proves the original same-query comparison with error `8/2^(p+4)`.
[GaussianGammaCanonicalTailShift](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTailShift.lean)
accounts for the retiming of the actual addition and proves the regular
name identity `T_N=L_(N+1)+T_(N+1)` at independent precisions.
[GaussianGammaExactTailDisk](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaExactTailDisk.lean)
constructs an equivalent regular tail name on the exact C6 disk and
proves its exponential bound when `R²≤N`.
[GaussianGammaCanonicalTailExponential](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTailExponential.lean)
proves that the actual tail exponential approaches one at a computed
cofinal cutoff. The original pure-tail finite sample comparison uses the
C6 radius and the finite three-Lipschitz estimate.
[GaussianGammaEulerHead](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerHead.lean)
builds the literal finite polynomial in C5 and C7, proves its finite
split and binds each factor to the local C4 constant. At cutoff `2R` its
Euclidean majorant is exactly the polynomial factor in C9.
[GaussianGammaEulerHeadLower](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerHeadLower.lean)
proves that the original pole guard gives the exact lower bound
`δ^(N+1)/N!` on the literal head. Its actual rational reciprocal
multiplies the head to one and satisfies the corresponding upper bound.
[GaussianBoundedInverseApartness](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianBoundedInverseApartness.lean)
computes a finite anchor for the original reciprocal-name program from
a bounded regular inverse and proves agreement with that inverse.
[GaussianGammaReciprocalInverse](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaReciprocalInverse.lean)
constructs the original reciprocal of C7 under the supplied pole guard.
It proves the C13 constant is positive and gives a regular multiplicative
inverse bounded by exactly `1/λ`. The actual Gamma observations obey
`1/λ+2/2^p`.
[GaussianApproximateInverseDistance](Lean/IPRADerivations/Analysis/Names/Rates/Reciprocals/GaussianApproximateInverseDistance.lean)
and [GaussianNamedInverseRate](Lean/IPRADerivations/Analysis/Names/Rates/Reciprocals/GaussianNamedInverseRate.lean)
transfer a direct comparison with base rate `D/N` to the exact inverse
rate `A²D/(B²N)` when both inverses have bounds `A/B`.
[GaussianNamedRateTransport](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedRateTransport.lean)
preserves the exact base rate across replacements by equivalent names.
[GaussianGammaEulerInverseConvergence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerInverseConvergence.lean)
instantiates the C15 rate `3M_R(R²+R)/(λ²N)` for the actual Euler
reciprocal and Gamma with independent observation errors.
[GaussianGammaEulerInverseApproximationName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerInverseApproximationName.lean)
constructs an actual cofinal sampler from this exact fractional
coefficient and proves that it gives the same regular name as Gamma.
[GaussianGammaRadiusOverlap](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaRadiusOverlap.lean)
proves agreement of the original C7 and Gamma names at the same
encoded rational point on two supplied disks. Gamma permits separate
pole certificates and actual computed anchors on the two disks.
[GaussianGammaCanonicalExponent](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalExponent.lean)
constructs the actual regular C7 exponent from the Euler constant mesh
name, the exact harmonic value and the original canonical tail at `2R`.
The computed zeroth-observation radius gives a regular exponential.
[GaussianGammaHarmonicIncrement](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaHarmonicIncrement.lean)
proves the exact scalar and Gaussian identity `H_(N+1)=H_N+1/(N+1)`
for the original harmonic programs.
[GaussianGammaCanonicalExponentBound](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalExponentBound.lean)
proves that every original C7 exponent observation lies in the numerical
disk of radius `2R²+2R`, using the original tail with its rounding error.
[GaussianGammaFixedEulerExponent](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFixedEulerExponent.lean)
constructs an exact representative in the same disk for the exponent
built from the fixed Euler observation and both finite-tail summands.
[GaussianGammaFixedEulerExponentBalance](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFixedEulerExponentBalance.lean)
proves the addition identity with the original Euler correction.
[GaussianGammaFoldedQBound](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFoldedQBound.lean)
then factors the original `Q_N` and gives its exact bounded representative.
[GaussianGammaEulerReciprocalInverse](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerReciprocalInverse.lean)
constructs its actual reciprocal on the pole-free disk using the same
C13 constant `λ`. The exact representative has bound `1/λ`.
[GaussianRationalLowerPerturbation](Lean/IPRADerivations/Analysis/Names/Rates/GaussianRationalLowerPerturbation.lean)
proves the exact Gaussian lower bound near one and the fractional lower
bound for one factor of a product.
[GaussianGammaObservationLower](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaObservationLower.lean)
uses them to bound the actual `P` and `Q_N` observations below by
`λ max(0,1−K/2^p)` and the Gamma observations below by
`(1/M_R) max(0,1−K/2^p)`. Each `K` is given by the corresponding
original multiplication clock.
[GaussianGammaPoleZeros](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleZeros.lean)
proves exact zero of the original C7 observations at each encoded
negative integer whose pole index is included in the head.
[GaussianGammaPoleSearch](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleSearch.lean)
proves the converse for encoded rational inputs. The bounded search
returns an exact pole index or derives separation with `δ=1/B` from
the nonzero translated integer norms. The actual reciprocal anchor
then excludes the original C7 zero predicate in the failure branch.
[GaussianGammaEulerHeadShift](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerHeadShift.lean)
proves the finite polynomial cancellation underlying C20 for all
numerical cutoffs. Its actual head output satisfies
`z H_N(z+1)=(z+N+1)H_N(z)` by multiplication alone.
[GaussianGammaEulerShift](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/GaussianGammaEulerShift.lean)
proves the corresponding shift for the original finite Euler names
with the actual `exp(−log N)` factor.
[GaussianGammaEulerShiftLimit](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/GaussianGammaEulerShiftLimit.lean)
computes the correction and its exact error under the mesh-log inverse
identity. [GaussianGammaFunctionalEquation](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaFunctionalEquation.lean)
proves the original C7 shift under that identity for all positive cutoffs.
[RationalReciprocalPowerTail](Lean/IPRADerivations/Analysis/RationalArithmetic/Powers/RationalReciprocalPowerTail.lean)
proves the C17 sharp finite tail for the actual reciprocal-power sum.
The bound retains the endpoint potential for every numerical length,
with exponent `m≥2` and starting index `N≥1`.
[RationalReciprocalPowerName](Lean/IPRADerivations/Analysis/Names/RationalReciprocalPowerName.lean)
gives the C17 cofinal zeta sampler and the shifted tail as regular names.
Each raw tail observation satisfies the exact sharp bound and is nonnegative.
The original finite reciprocal-power prefix plus this tail reconstructs the
same zeta name at independent observation precisions.
[GaussianGammaFiniteDegreeRearrangement](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaFiniteDegreeRearrangement.lean)
proves the finite C16 degree rearrangement for the actual normalized tail.
Its returned PR program computes both equal rectangle values, and the
original `R²/N` bound applies to the value.
[GaussianGammaReciprocalDegreeCells](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaReciprocalDegreeCells.lean)
separates each literal degree column into its signed monomial and the
actual rational reciprocal-power partial sum.
[GaussianGammaDegreeTail](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaDegreeTail.lean)
proves the exact C18 error `R²/(N·2^(L+1))` between finite rectangles
of degrees `L+2` and `L+J+2`, including the original `N=2R` choice.
[GaussianGammaFixedDegreeHorizon](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaFixedDegreeHorizon.lean)
proves the exact change with factor horizon at a fixed degree and
constructs its regular cofinal name with the original factor clock.
[GaussianGammaCofinalDegreeTail](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaCofinalDegreeTail.lean)
proves the same C18 error against the original cofinal tail at independent
precisions, with the two requested observation errors.
[GaussianGammaZetaDegreeName](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaZetaDegreeName.lean)
identifies the original fixed-degree tail with the actual C17 zeta-tail
polynomial, retaining the exact C18 bound.
[GaussianGammaZetaTailSeries](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaZetaTailSeries.lean)
uses the cofinal degree `L_p=p+R²` to construct the actual C16 zeta series
and proves its equivalence with the original tail at independent
precisions, including the source cutoff `N=2R`.
[GaussianFiniteExponentialCoefficientMajorant](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianFiniteExponentialCoefficientMajorant.lean)
proves the finite weighted coefficient bound for the original polynomial
exponential. [GaussianWeightedPolynomialTail](Lean/IPRADerivations/Analysis/Polynomials/Taylor/GaussianWeightedPolynomialTail.lean)
proves the finite C19 geometric tail on the rescaled half disk. The
Comparison of coefficient names across radii and cofinal analyticity remain.
[GaussianGammaZetaCoefficientPolynomial](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaZetaCoefficientPolynomial.lean)
constructs the actual degree buffer and binds its Horner value to the
original C16 polynomial at its original clock.
[GaussianGammaZetaCoefficientNorm](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaZetaCoefficientNorm.lean)
derives the original sampled weighted coefficient bound
`R^m/(m(m−1)N^(m−1))` for each `m≥2`.
[GaussianGammaZetaWeightedNorm](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaZetaWeightedNorm.lean)
sums the original stored coefficients to prove the full finite tail
mass `R²/N` for every cutoff and observation precision.
[GaussianGammaLinearCoefficient](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaLinearCoefficient.lean)
checks the original sampled Euler-linear monomial and its mass
`R(N+1)`.
[GaussianGammaExponentCoefficientPolynomial](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaExponentCoefficientPolynomial.lean)
combines the original sampled exponent coefficients and bounds the
weighted mass of their finite exponential at cutoff `2R`.
[GaussianGammaEulerFactorPolynomial](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerFactorPolynomial.lean)
evaluates the actual stored two-entry Euler factor.
[GaussianGammaEulerHeadPolynomial](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerHeadPolynomial.lean)
builds the actual head by coefficient convolution and proves weighted
mass at most `R(1+R)^N`.
[GaussianGammaFiniteCoefficientPolynomial](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaFiniteCoefficientPolynomial.lean)
evaluates the full finite product of the original head and sampled
finite exponential. Its exact weighted coefficient majorant is the
original `M_R`. A prefix through degree `d` has discarded-tail
error at most `M_(2R)/2^(d+1)` on the radius-`R` disk.
[GaussianGammaSynchronousExponentName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaSynchronousExponentName.lean)
proves that a regular sampler evaluates the same sampled exponent
coefficient buffer with clocks determined solely by radius and precision.
[GaussianGammaSynchronousExponentCompatibility](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaSynchronousExponentCompatibility.lean)
identifies that sampler with the original C7 exponent at independent
precisions on the original disk.
[GaussianBoundedConstantProductName](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianBoundedConstantProductName.lean)
then provides a regular multiplication clock depending only on the
numerical bound for the constant. This lets the finite coefficient
sampler multiply by the original head with an argument-independent clock.
[GaussianGammaCofinalCoefficientName](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaCofinalCoefficientName.lean)
binds the resulting observations to the original computed coefficient
polynomials and the original C7 name. All three coefficient clocks depend
solely on radius and precision.
[GaussianGammaOriginalC19Prefix](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/OriginalPrefixes/GaussianGammaOriginalC19Prefix.lean)
compares the computed degree prefix directly to the original C7 name
with the exact C19 degree bound and independent observation errors.
[GaussianGammaPolynomialConstantLinear](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaPolynomialConstantLinear.lean)
checks the actual constant and linear coefficients of the cofinal
polynomial as zero and one.
[GaussianPolynomialLinearFactorCoefficients](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianPolynomialLinearFactorCoefficients.lean)
checks the original quadratic coefficient under a linear factor.
[GaussianPolynomialExponentialLinear](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianPolynomialExponentialLinear.lean)
proves preservation of the linear coefficient by the actual finite
exponential when the input constant coefficient is zero.
[GaussianGammaEulerHeadQuadratic](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerHeadQuadratic.lean)
identifies the quadratic entry of the Euler head with the harmonic sum.
[GaussianGammaPolynomialQuadratic](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaPolynomialQuadratic.lean)
identifies the exact cofinal quadratic coefficient name with the
original Euler–Mascheroni name.
[GaussianGammaFiniteQuadraticExpansion](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaFiniteQuadraticExpansion.lean)
bounds the remainder of the unchanged finite polynomial by a cubic
in the shrinking input radius.
[GaussianGammaQuadraticSampler](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaQuadraticSampler.lean)
extends that bound to the original reciprocal Gamma observations. The
independent Euler–Mascheroni observation error retains its quadratic
input-radius factor.
[GaussianGammaExponentCoefficientStability](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaExponentCoefficientStability.lean)
proves fixed exponent-coefficient equality across degree horizons
at the same sample precision and Euler cutoff.
[GaussianPolynomialExponentialCapStability](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianPolynomialExponentialCapStability.lean)
checks that each original finite exponential coefficient is unchanged
across caps at least its exponent for zero constant input.
[GaussianPolynomialLowJetProduct](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianPolynomialLowJetProduct.lean)
transfers coefficient agreement through the actual product of buffers
with different stored degrees.
[GaussianGammaPowerHorizonCoherence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaPowerHorizonCoherence.lean),
[GaussianGammaExponentialHorizonCoherence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaExponentialHorizonCoherence.lean),
and [GaussianGammaFiniteCoefficientStability](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaFiniteCoefficientStability.lean)
reduce every literal cofinal coefficient observation to the actual fixed
coefficient at its degree-sized truncations and original precision clock.
[GaussianPolynomialPowerNormVariation](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianPolynomialPowerNormVariation.lean)
checks the perturbation bound for the actual finite power cursor.
[GaussianPolynomialExponentialCoefficientVariation](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianPolynomialExponentialCoefficientVariation.lean)
preserves each factorial weight in the original finite exponential
coefficient error.
[GaussianGammaInputPrecisionNorm](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaInputPrecisionNorm.lean)
proves the actual input coefficient buffer error across precisions.
[GaussianGammaInputStaticNorm](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaInputStaticNorm.lean)
gives its canonical fixed-degree norm envelope.
[GaussianGammaFixedCoefficientVariation](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaFixedCoefficientVariation.lean)
derives a computed precision modulus for the full actual fixed
coefficient for every degree.
[GaussianGammaHigherCoefficientName](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaHigherCoefficientName.lean)
constructs a regular name at every degree from the unchanged cofinal
coefficient sampler at radius `e+1`.
[GaussianGammaRadiusCoefficientName](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaRadiusCoefficientName.lean)
keeps the radius as an actual input.
[GaussianGammaAllDegreeCoefficientStability](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaAllDegreeCoefficientStability.lean)
and [GaussianGammaAllDegreeCoefficientVariation](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaAllDegreeCoefficientVariation.lean)
remove the head-degree restriction by exact product coefficient
preservation under padding. The unchanged name is regular for every
internal degree at any fixed positive radius.
[GaussianLagrangeInterpolation](Lean/IPRADerivations/Analysis/Polynomials/Interpolation/GaussianLagrangeInterpolation.lean)
recovers finite original coefficients from actual natural-grid observations.
[GaussianLagrangeCoefficientSensitivity](Lean/IPRADerivations/Analysis/Polynomials/Interpolation/GaussianLagrangeCoefficientSensitivity.lean)
computes the error gain of the original inverse row.
[GaussianShrinkingPolynomialTail](Lean/IPRADerivations/Analysis/Polynomials/Taylor/GaussianShrinkingPolynomialTail.lean)
retains the exact power of the shrinking radius in the finite tail bound.
[GaussianShrinkingGridValueRecovery](Lean/IPRADerivations/Analysis/Names/Approximation/GaussianShrinkingGridValueRecovery.lean)
uses the original full polynomial values on the shrinking grid. The
checked low-prefix program and exact rational dilation give a bound
for the difference of the actual coefficients.
[GaussianGammaUnitCoefficientMass](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaUnitCoefficientMass.lean)
bounds the total ordinary coefficient norm of each original polynomial.
[GaussianGammaCoefficientRadiusIndependence](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaCoefficientRadiusIndependence.lean)
proves that the actual coefficient names agree at every pair of positive
radii, including the original canonical radius.
[GaussianGammaOriginalPrefixName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/OriginalPrefixes/GaussianGammaOriginalPrefixName.lean)
regularizes the unchanged original finite prefix and proves its literal
C19 approximation bound with independent precisions.
[GaussianGammaCanonicalPrefixName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalPrefixName.lean)
supplies the regular finite evaluator of the original canonical names.
[GaussianGammaCanonicalPrefixTaylor](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalPrefixTaylor.lean) compares the actual original finite C19 polynomial
to the finite sum of actual canonical coefficient observations at any
internal order. Its remainder retains the full power of the shrinking
input radius, with separate finite-cutoff and coefficient-query errors.
[GaussianGammaCanonicalTaylorSampler](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalTaylorSampler.lean) removes the auxiliary finite-polynomial query from the bound
for the original reciprocal Gamma sampler. The resulting error is the
shrinking tail plus one output observation error and the coefficient
observation error multiplied by the number of retained terms.
[GaussianGammaDeflatedPrefixTaylor](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/OriginalPrefixes/GaussianGammaDeflatedPrefixTaylor.lean) factors the exact canonical prefix by its argument and
checks the value one at zero for the deflated prefix.
[GaussianGammaShiftedDeflatedPolynomial](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/Taylor/GaussianGammaShiftedDeflatedPolynomial.lean) factors the original full Euler polynomial and compares
its deflated value with the shifted reciprocal Gamma at independent
precisions on the certified nonzero native guard.
[GaussianGammaShiftedDeflatedName](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/Taylor/GaussianGammaShiftedDeflatedName.lean) packages this comparison as a regular name through a
computed retiming and proves equivalence to the original shifted name.
[GaussianGammaShiftedDeflatedZero](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/Taylor/GaussianGammaShiftedDeflatedZero.lean) evaluates the same deflated polynomial and shifted reciprocal
name at the native zero input.
[GaussianGammaShiftedDeflatedIdentification](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/Taylor/GaussianGammaShiftedDeflatedIdentification.lean) proves the same original name equivalence over the full
native source, including zero. [GaussianGammaDeflatedFiniteTaylor](Lean/IPRADerivations/Analysis/Gamma/Taylor/GaussianGammaDeflatedFiniteTaylor.lean) proves the true deflated
polynomial remainder with the full power of the shrinking radius.
[GaussianGammaShiftedTaylorSampler](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/Taylor/GaussianGammaShiftedTaylorSampler.lean) transfers that remainder to the original shifted reciprocal
Gamma observation at every internal order. It retains the original
canonical coefficient observations and their independent clock, and
covers zero increment.
[GaussianGammaPrefixCompatibility](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/OriginalPrefixes/GaussianGammaPrefixCompatibility.lean)
identifies the two prefix names and proves the literal C19 rate with
these canonical coefficients on the original encoded disk.
[GaussianRobinOddLogarithm](Lean/IPRADerivations/Analysis/Logarithm/Robin/GaussianRobinOddLogarithm.lean)
and [GaussianRobinLogarithmParity](Lean/IPRADerivations/Analysis/Logarithm/Robin/GaussianRobinLogarithmParity.lean)
identify the original finite Robin artanh component with the difference of
the two original local logarithm polynomials evaluated at opposite rational
inputs. [GaussianRobinOddLogarithmName](Lean/IPRADerivations/Analysis/Logarithm/Robin/GaussianRobinOddLogarithmName.lean)
constructs a regular sampler from the stored odd series and proves
its equivalence with the actual difference of the two regular local
logarithm names.
[GaussianRobinOddExponential](Lean/IPRADerivations/Analysis/Exponential/IntegerPowers/GaussianRobinOddExponential.lean)
identifies the actual exponential of that odd name with the constant
`(b+a)/(b−a)` on the half disk.
[GaussianRobinLogRangeReduction](Lean/IPRADerivations/Analysis/SpecialFunctions/LambertW/GaussianRobinLogRangeReduction.lean)
identifies the actual exponentials of the original two binary components
as `2` and `a/Bt(a,b)`.
[GaussianRobinLowerDecomposition](Lean/IPRADerivations/Analysis/SpecialFunctions/LambertW/GaussianRobinLowerDecomposition.lean)
proves the exact decomposition of the original stored lower endpoint at
every numerical cutoff into the two actual odd sums and the binary exponent.
[GaussianRobinMeshLogDecomposition](Lean/IPRADerivations/Analysis/SpecialFunctions/LambertW/GaussianRobinMeshLogDecomposition.lean)
identifies their named weighted sum with the original mesh logarithm
at independent observation precisions.
[GaussianNamedNaturalScale](Lean/IPRADerivations/Analysis/Names/Scaling/GaussianNamedNaturalScale.lean)
and [GaussianNaturalScaleProductName](Lean/IPRADerivations/Analysis/Names/Scaling/GaussianNaturalScaleProductName.lean)
identify the actual retimed scaling with named multiplication.
[GaussianRobinIntegerExponential](Lean/IPRADerivations/Analysis/Exponential/IntegerPowers/GaussianRobinIntegerExponential.lean)
proves the exponential law for every numerical binary exponent by
quantifier-free induction on a finite error comparison.
[GaussianMeshLogSign](Lean/IPRADerivations/Analysis/Inequalities/GaussianMeshLogSign.lean)
checks the exact named negation and reciprocal transport.
[GaussianRobinMeshExponential](Lean/IPRADerivations/Analysis/Exponential/IntegerPowers/GaussianRobinMeshExponential.lean)
combines the original range-reduced components and proves
`exp(log N)=N` and `exp(−log N)=1/N` for the original mesh name.
This proves C20 with its original disk conditions.
[GaussianGammaNormalization](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaNormalization.lean)
uses the original Euler head at one and the finite convergence rate
to prove `P(1)=1` and `Γ(1)=1` once the mesh identity is supplied.
[GaussianGammaShift](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/GaussianGammaShift.lean)
uses the reciprocal shift and checked inverse product to prove
`Γ(z+1)=zΓ(z)` on the recorded original two pole-free domains.
[GaussianGammaShiftTrajectory](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/GaussianGammaShiftTrajectory.lean)
constructs the actual native successor trajectory, proves its disk at
every numerical stage, and identifies its encoded coordinate values.
[GaussianGammaFactorialValues](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Factorials/GaussianGammaFactorialValues.lean)
then proves the original C21 factorial identity for all internal indices.
[GaussianGammaRepeatedShift](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Recurrence/GaussianGammaRepeatedShift.lean)
proves C22 for the original reciprocal Gamma name and the actual rising
product, including zero factors.
[GaussianGammaRisingFactorial](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Factorials/GaussianGammaRisingFactorial.lean)
proves V8 for the original Gamma names wherever both endpoints have
certified pole margins. Every internal index is allowed, including zero.
The observation program returns the actual rising product and the two
sides of the identity at independent precisions.
[GaussianGammaBinomialCleared](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaBinomialCleared.lean)
proves the entire cleared V9 identity using the actual generalized
binomial polynomial, including its values at apparent cancelled poles.
[GaussianGammaBinomialQuotient](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaBinomialQuotient.lean)
identifies the actual formal Gamma quotient with that polynomial
where the two original Gamma endpoint guards hold. Both proofs
allow every internal index, including zero.
[GaussianGammaLocalPoleGuards](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaLocalPoleGuards.lean)
derives the original punctured-disk domain for C24 and the separated
terminal argument `1+h/B`.
[GaussianGammaPoleFiniteFactors](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleFiniteFactors.lean)
identifies the actual reversed rising factors with the signed factorial
times the finite normalized correction product.
[GaussianGammaPoleMultiplier](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleMultiplier.lean)
checks the inverse step and the actual finite product of inverse factors.
[GaussianGammaLocalPoleFormula](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaLocalPoleFormula.lean)
proves C24 and its cleared form for the original Gamma names at every
encoded rational increment in the punctured unit disk. It computes
both margins from the integer squared norm of the increment.
[GaussianGammaPoleFactorContinuity](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleFactorContinuity.lean)
proves the explicit rational error of the original finite normalized
factor product near the pole.
[GaussianGammaPoleReciprocalFactor](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleReciprocalFactor.lean)
proves the original C23 factorization throughout the encoded closed
unit disk.
[GaussianGammaPoleQuotientCenter](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleQuotientCenter.lean)
and [GaussianGammaPoleCenterValue](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleCenterValue.lean)
check the exact center values of the reciprocal quotient and regularized
Gamma name against the signed factorial and signed inverse factorial.
[GaussianGammaPoleInverseContinuity](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleInverseContinuity.lean)
proves the corresponding actual inverse-factor perturbation bound on
the half disk.
[GaussianGammaTerminalContinuity](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaTerminalContinuity.lean)
proves the fixed half-disk certificate for the actual terminal argument
and transfers an independent C7 rate at one to the original Gamma name.
[GaussianGammaPoleProductRate](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleProductRate.lean),
[GaussianGammaPoleLimitTransport](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleLimitTransport.lean),
and [GaussianGammaPoleLimitModulus](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleLimitModulus.lean)
derive both local product observations at a common computed precision
from a specified terminal C7 rate.
[GaussianGammaPoleDifferenceQuotient](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleDifferenceQuotient.lean)
binds the factored quotient to the actual division on the punctured disk.
[GaussianGammaPoleLimits](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleLimits.lean)
derives the terminal rate and proves the C23 and C25 dyadic limits of
the actual divided reciprocal and the original cleared Gamma on encoded
rational increments. The bound holds for every later observation.
[GaussianRationalConjugation](Lean/IPRADerivations/Analysis/RationalArithmetic/GaussianRationalConjugation.lean)
proves exact conjugation for rational code, metric and scalar Taylor sums.
[GaussianGammaFiniteConjugation](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaFiniteConjugation.lean)
proves covariance of the original finite head, local factors and literal
prefix for C26.
[GaussianNameConjugation](Lean/IPRADerivations/Analysis/Names/GaussianNameConjugation.lean)
transports conjugation through the actual regular-name operations.
[GaussianGammaNameConjugation](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaNameConjugation.lean)
proves conjugation of the original C7 reciprocal via the literal C11
cofinal Weierstrass sampler, including at every zero of the original head.
[GaussianGammaInverseConjugation](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaInverseConjugation.lean)
proves conjugation for the same pole-free Gamma inverse.
[GaussianGammaRealValues](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaRealValues.lean)
constructs actual rational regular names for the real values of both
original Gamma names at encoded real rational inputs.
[GaussianGammaFiniteValueProperness](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaFiniteValueProperness.lean)
and [GaussianGammaInputProperness](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaInputProperness.lean)
prove that equality of the native coordinate values at a fixed denominator
is respected by the original reciprocal and pole-free Gamma names.
[GaussianGammaEulerHeadContinuity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerHeadContinuity.lean)
proves the actual finite head modulus on each fixed-radius disk for
two encodings with the same denominator.
[GaussianGammaEncodingRescaling](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaEncodingRescaling.lean)
proves C7 agreement under positive rescaling of both numerator and
denominator, including all positive encodings of one.
[GaussianGammaLogExponentContinuity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaLogExponentContinuity.lean)
and [GaussianGammaEulerContinuityReference](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaEulerContinuityReference.lean)
derive the original C7 comparison with a finite shared reference and
bound the reference variation in the input.
[GaussianGammaInputContinuity](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaInputContinuity.lean)
derives the uniform input modulus for the original C7 name from this
reference. It preserves independent observation errors.
[GaussianGammaC7Name](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaC7Name.lean)
multiplies it by the original polynomial head and gives a regular name
for the displayed C7 expression on each fixed input disk.
[GaussianGammaCutoffName](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaCutoffName.lean)
verifies the same programs at arbitrary numerical cutoffs satisfying
`N≥1` and `2R≤N`, with literal specialization at `N=2R`.
[GaussianGammaC9Bound](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaC9Bound.lean)
proves the exact C9 bound `M_R` for every observation of the original
reciprocal name. [GaussianGammaFoldedMajorantExponent](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFoldedMajorantExponent.lean)
constructs the same bound for a representative formed from the original
head and the exponent at `2R` minus the tail at `N`.
[GaussianGammaFoldedC9Bound](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFoldedC9Bound.lean)
identifies this bounded representative with the original folded finite
`P_N` program. Its original observations obey `M_R+2/2^p`.
[GaussianGammaFiniteApproximantName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Approximants/GaussianGammaFiniteApproximantName.lean)
constructs the folded C5 names from the original polynomial head,
Euler constant, harmonic value, and harmonic-mesh logarithm. It proves the
actual sampling equations and regularity.
[GaussianGammaWeierstrassFactors](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Weierstrass/GaussianGammaWeierstrassFactors.lean)
checks the literal finite products at a common Taylor cutoff.
[GaussianGammaWeierstrassFiniteName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Weierstrass/GaussianGammaWeierstrassFiniteName.lean)
normalizes the actual factor fold and compares it to the negative
harmonic exponential.
[GaussianGammaWeierstrassApproximant](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaWeierstrassApproximant.lean)
attaches the original Euler-constant exponential and identifies the
literal factor-by-factor name with the original folded `P_N`.
[GaussianGammaWeierstrassConvergence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Weierstrass/GaussianGammaWeierstrassConvergence.lean)
proves that the folded name approaches C7 at rate `3M_R R²/N`.
[GaussianGammaWeierstrassLimit](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Weierstrass/GaussianGammaWeierstrassLimit.lean)
transfers the exact rate to the literal factor program and evaluates
it at a computed cofinal cutoff. The resulting actual regular sampler
agrees with the original C7 reciprocal at independent precisions.
[GaussianGammaLogHarmonicName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaLogHarmonicName.lean)
proves that the actual sum of the fixed-index Euler and harmonic-mesh
logarithm names agrees with the exact harmonic constant at independent
precisions.
[GaussianGammaExponentStep](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaExponentStep.lean)
proves the actual exponent identity for adjacent cutoffs by combining
the harmonic increment, tail shift and original local full logarithm.
[GaussianGammaAdjacentCutoff](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaAdjacentCutoff.lean)
uses local C4 and the literal head successor to prove agreement of the
complete C7 names at adjacent cutoffs, including zeros of the polynomial
head. [GaussianGammaFoldedApproximantBalance](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaFoldedApproximantBalance.lean)
proves both C8 product identities for the actual folded programs.
[GaussianGammaCutoffIndependence](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaCutoffIndependence.lean)
uses quantifier-free induction at fixed observation precision, followed
by an envelope comparison, to derive agreement at any two valid
numerical cutoffs. [GaussianGammaEulerCorrectionDisk](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerCorrectionDisk.lean)
proves the exact `R/N` disk for the represented Euler correction.
[GaussianGammaPerturbationExponent](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Exponents/GaussianGammaPerturbationExponent.lean)
proves the actual difference-of-exponents envelope at `(R²+R)/N`
and its relation to the original correction.
[GaussianGammaEulerConvergence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerConvergence.lean)
combines the two C8 product identities by multiplication and proves the
C10 bound `3M_R(R²+R)/N` with the two ordinary independent observation
errors. [GaussianGammaEulerApproximationName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerApproximationName.lean)
chooses a numerical cutoff and one additional observation bit to
construct an actual regular cofinal Euler sampler equivalent to the
original reciprocal name.

[GammaCanonicalRemainder](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GammaCanonicalRemainder.lean)
proves the sharp finite C3 remainder between cutoffs `L` and `L+K` of the
actual factor at the same rational argument. The cleared scale is
`(L+3)N^(L+2)(N-R)`, and the right-hand radius power is `R^(L+3)`.
The returned PR5 data retain both original positive denominators and the
certificate proves the positivity of this scale under `R<N`.

[GammaLocalFactorName](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GammaLocalFactorName.lean)
constructs the actual local-factor name on `N≥1`, `|z|≤R` and `2R≤N`.
It gives a PR4 signed dyadic observation at scale `2^(p+4)`, proves
regularity at independent precisions, and gives the disk bound
`R²/N² + 2/2^(p+4)`. The sharp finite C3 bound also compares an original
fixed cutoff with a cofinal name observation, with explicit rounding
slack. The original logarithm and its exponential are identified below.

The reusable [ReciprocalSquareTail](Lean/IPRADerivations/Analysis/Series/ReciprocalSquares/ReciprocalSquareTail.lean)
provides the underlying uniform rational inverse-square comparison.
The [complex logarithm modules](Lean/IPRADerivations/Analysis/Logarithm/ComplexLogarithmName.lean)
construct a different canonical local power-series name and its exact
rounding/Cauchy bounds; they do not automatically instantiate Gamma's Euler
approximants, elementary function error budgets, or branch/domain contracts.

[LogarithmExponentialCoefficients](Lean/IPRADerivations/Analysis/Exponential/Polynomials/LogarithmExponentialCoefficients.lean)
now proves a finite algebraic dependency of C4. Its actual signed Bell/history
program uses the proved kernel `g_k=(-1)^k k!`, and derives the differential
coefficient recurrence, initial values and zero coefficients at every
internal degree at least two. The rational coefficients use proved-positive
factorials. The low coefficients of the literal finite sum of powers of the
truncated logarithm are identified below. Transport to the actual analytic
exponential and logarithm names requires their tail bounds.

[FiniteExponential](Lean/IPRADerivations/Analysis/Exponential/FiniteExponential.lean)
and [FiniteLogarithm](Lean/IPRADerivations/Analysis/Logarithm/FiniteLogarithm.lean)
now evaluate the literal factorial-cleared finite sums, together with
independent termwise derivative sums. Exact coefficient clearing identifies
the prescribed `1/k!` and alternating `1/j` coefficients. Internal-cutoff
QF inductions derive their evaluation recurrences and exact differential
residuals `D E'_N+x^N=E_N` and
`(D+x)H'_N+g_N x^N=N!D^N`. Positive-denominator and actual PR3 output
contracts are checked. The complex composition, coefficient bounds, tails,
and original logarithm name identity follow in the modules below.

[GaussianRationalPolynomialPowers](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalPolynomialPowers.lean)
provides the stored Gaussian-rational power buffers needed for the literal
finite composition. With the original coefficient length, the computed
buffer evaluates to the corresponding power of the original Horner value.
Every in-range successor also has the actual convolution coefficient law.
[GaussianRationalPolynomialExponential](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponential.lean)
constructs the actual factorial-weighted coefficient sum. Its Horner
evaluation is the literal finite complex exponential sum of the original
value.

[GaussianFiniteLogarithmPolynomial](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmPolynomial.lean)
constructs the original truncated logarithm polynomial and identifies each
stored coefficient with the original factorial kernel. Its actual finite
exponential composition has the literal finite complex Horner value.
[GaussianIntegerFractionPowers](Lean/IPRADerivations/Analysis/RationalArithmetic/GaussianIntegerFractionPowers.lean)
proves the exact fraction powers and signed factorial numerator.
[GaussianFiniteLogarithmSampler](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmSampler.lean)
identifies the value of the same logarithm polynomial with the original
cleared numerator and denominator.
[GammaLogarithmFactorBridge](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GammaLogarithmFactorBridge.lean)
identifies that sample with the sum of the original linear term and
the original canonical factor and evaluates the actual finite exponential
composition at that argument. The low-degree coefficients and analytic tail
are checked below.
[GaussianRationalLowCoefficientConvolution](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalLowCoefficientConvolution.lean)
identifies low coefficients of the actual stored polynomial product with
their finite ascending Cauchy sums.
[GaussianRationalPolynomialPowerSupport](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalPolynomialPowerSupport.lean)
uses that identity to derive the zero coefficients below the original
power exponent.
[GaussianRationalPolynomialExponentialStability](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialStability.lean)
proves that the actual low coefficient of the original composition is
already attained at the stage indexed by that coefficient. The remaining
coefficient comparison is with the Bell recurrence.
[GaussianRationalPolynomialExponentialCoefficients](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialCoefficients.lean)
identifies the same coefficient with the exact inverse-factorial-weighted
sum of stored power coefficients.
[GaussianRationalWeightedCoefficientConvolution](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalWeightedCoefficientConvolution.lean)
derives the exponent-weighted product rule on those same low coefficients.
[GaussianRationalEulerCoefficients](Lean/IPRADerivations/Analysis/Polynomials/Coefficients/GaussianRationalEulerCoefficients.lean)
stores the actual exponent-weighted coefficients, implements the product rule
with the actual output buffers, and derives the alternating unit Euler
coefficients of the original logarithm.
[GaussianRationalPolynomialPowerEuler](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalPolynomialPowerEuler.lean)
derives the exact Euler rule for the low coefficients of the original stored
powers, including the source logarithm.
[GaussianRationalFactorialEulerSums](Lean/IPRADerivations/Analysis/Inequalities/GaussianRationalFactorialEulerSums.lean)
shifts the exact factorial-weighted sum after applying that rule to the
original composition.
[GaussianRationalExponentialProductCoefficients](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianRationalExponentialProductCoefficients.lean)
identifies the shifted finite sum with the actual product of the Euler-weighted
base and the accumulated exponential.
[GaussianRationalFiniteExponentialEuler](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianRationalFiniteExponentialEuler.lean)
combines power support with the exact cutoff to derive the finite exponential
Euler rule for the original logarithm at every exponent within both cutoffs.
[GaussianRationalCoefficientRecursion](Lean/IPRADerivations/Analysis/Polynomials/Coefficients/GaussianRationalCoefficientRecursion.lean)
proves bounded uniqueness for an actual prior-coefficient recursion.
[GaussianFiniteLogarithmCoefficientRecursion](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmCoefficientRecursion.lean)
derives that recursion and its initial value on the original stored
composition.
[GaussianFiniteLogarithmLinearRecursion](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmLinearRecursion.lean)
verifies the same recurrence on the actual two-coefficient linear buffer.
[GaussianFiniteLogarithmBellIdentification](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmBellIdentification.lean)
then identifies the coefficients of the literal finite composition with the
original signed Bell values at each exponent within both internal cutoffs.
[GaussianFiniteLogarithmCompositionTail](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmCompositionTail.lean)
derives the actual residual from the stored high coefficients and bounds its
size on the source half-disk using the computed stage coefficient budget.
A uniform weighted majorant remains necessary for the analytic modulus.
[GaussianRationalPolynomialDilation](Lean/IPRADerivations/Analysis/Polynomials/Representation/GaussianRationalPolynomialDilation.lean)
constructs the actual scaled-argument buffer and proves the weighted
coefficient arithmetic used to produce that majorant.
[GaussianFiniteLogarithmWeightedNorm](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmWeightedNorm.lean)
bounds the actual truncated logarithm at auxiliary weight 5/9 by 65/72
for every original truncation degree.
[GaussianFiniteExponentialWeightedNorm](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianFiniteExponentialWeightedNorm.lean)
then bounds the weighted norm of the original finite exponential composition
by 72/7 at the same auxiliary weight. Convergence at the source disk still
requires the tail and truncation comparisons.
[GaussianRationalUnitDiskHornerNorm](Lean/IPRADerivations/Analysis/Polynomials/Horner/GaussianRationalUnitDiskHornerNorm.lean)
uses the original Horner size bound to control each prefix of the same
dilated composition by 11 at the rescaled source argument of radius at most
9/10.
[GaussianFiniteLogarithmGeometricTail](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmGeometricTail.lean)
identifies the actual high-prefix residual after subtracting the linear part
and bounds it on the original half-disk by the geometric tail. The passage
to a dyadic error bound is checked by
[GaussianFiniteLogarithmDyadicTail](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmDyadicTail.lean).
[GaussianFiniteLogarithmCompositionName](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmCompositionName.lean)
constructs the regular cofinal name from the original finite Gamma-factor
samples and proves its equivalence to the constant name `1+w`.
[GaussianRationalExponentialTail](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianRationalExponentialTail.lean)
proves the original scalar-sum cutoff comparison on a bounded Gaussian
rational input. [GaussianRationalExponentialName](Lean/IPRADerivations/Analysis/Exponential/GaussianRationalExponentialName.lean)
constructs the original cutoff name at such queries.
[GaussianRationalExponentialLipschitz](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianRationalExponentialLipschitz.lean)
proves the uniform three-Lipschitz estimate for the original finite
scalar exponential on the unit disk.
[GaussianRationalRadiusExponentialLipschitz](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianRationalRadiusExponentialLipschitz.lean)
proves the cutoff-dependent Lipschitz estimate on any numerical disk
and bounds it by the computed binary precision factor.
[GaussianRadiusExponentialName](Lean/IPRADerivations/Analysis/Exponential/GaussianRadiusExponentialName.lean)
uses that factor to compute the sampling clock for an actual regular
exponential on any fixed numerical disk. The exponential preserves
independent-precision equivalence of input names on that disk.
[GaussianScalarExponentialDiagonal](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianScalarExponentialDiagonal.lean)
proves that the actual triangular Cauchy sum is exactly the original
finite scalar exponential of the sum.
[GaussianScalarExponentialProductLowDegrees](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianScalarExponentialProductLowDegrees.lean)
binds the original rectangular product and identifies its exact difference
with the sum of its actual high-degree coefficients.
[GaussianScalarExponentialProductTail](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianScalarExponentialProductTail.lean)
proves the requested dyadic error of that actual high part at a computed
cutoff. [GaussianExponentialReference](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianExponentialReference.lean)
compares each actual observation with the original finite sum at a common
later input and cutoff. [GaussianExponentialAddition](Lean/IPRADerivations/Analysis/Exponential/GaussianExponentialAddition.lean)
uses the original addition and multiplication clocks to prove
`exp(u+v)=exp(u)exp(v)` at independent observation precisions on a common
numerical disk with `R≥1`.
[GaussianExponentialRadiusIndependence](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianExponentialRadiusIndependence.lean)
proves exponential properness with independent input disks and agreement
with the actual specialized unit-disk exponential.
[GaussianExponentialInverse](Lean/IPRADerivations/Analysis/Exponential/GaussianExponentialInverse.lean)
proves that multiplying the exponential of the original name by the
exponential of its actual negative gives the constant one.
[GaussianExponentialDiskMajorant](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianExponentialDiskMajorant.lean)
transfers the actual finite series on the nonnegative real axis to a
Euclidean bound throughout the disk.
[GaussianPositiveExponentialProduct](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianPositiveExponentialProduct.lean)
proves positivity of the original high-degree part and submultiplicativity
of the real finite sums.
[GaussianPositiveExponentialMajorant](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianPositiveExponentialMajorant.lean)
uses those positive sums and the unit factorial bound to prove `3^R`
for the original finite exponential on the entire numerical disk at
every cutoff.
[GaussianUnitDiskExponentialName](Lean/IPRADerivations/Analysis/Exponential/GaussianUnitDiskExponentialName.lean)
uses the actual scalar sums to construct a regular exponential of an
argument name with unit-disk samples and proves preservation of name
equivalence.
[GaussianExponentialSmallPerturbation](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianExponentialSmallPerturbation.lean)
proves the finite and named bound `3A/B` from one under a disk bound
`A/B≤1`. The product estimate for a bounded prefactor is `3MA/B`,
including at zeros. [GaussianExactDiskShrinking](Lean/IPRADerivations/Analysis/Geometry/DiskNames/GaussianExactDiskShrinking.lean)
constructs an equivalent name with exact disk radius from a bound with
dyadic observation slack. [GaussianExactDiskExponential](Lean/IPRADerivations/Analysis/Exponential/GaussianExactDiskExponential.lean)
transports this correction through the actual exponential programs.
[GaussianNamedSmallPerturbationTransport](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedSmallPerturbationTransport.lean)
proves the prefactor estimate at independent precisions using the
actual original multiplication clock.
[GaussianLocalLogarithmName](Lean/IPRADerivations/Analysis/Logarithm/Local/GaussianLocalLogarithmName.lean)
proves regularity and the unit-disk bound on every original unshifted
logarithm observation.
[GaussianLocalLogarithmExponentialIdentity](Lean/IPRADerivations/Analysis/Exponential/GaussianLocalLogarithmExponentialIdentity.lean)
then compares the actual exponential of that name with the constant name
`1+z/N` in both the cross and diagonal relations on the original half-disk
with `N≥1`. It also proves equivalence with the actual cofinal finite
composition. These are object-theory derivations of the local C4 identity.

### Checked Euler quadrature

[GaussianEulerExponentCompactBounds](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerExponentCompactBounds.lean)
bounds the original exponent on the compact interval and follows both
program clocks. [GaussianEulerCompactModulus](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactModulus.lean)
derives the local sampled modulus for the unchanged Euler integrand from
the positive rational time interval and the native bound on the complex
parameter. [GaussianGammaEulerCompactQuadrature](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaEulerCompactQuadrature.lean)
supplies the actual fixed-interval quadrature name at the prescribed
Gamma endpoints. Its checked modulus uses a larger mesh factor than the
paper’s proposed derivative bound.

[GaussianEulerDecayQuadraturePrecision](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayQuadraturePrecision.lean)
proves the decay endpoint estimate with independent observation
precisions and the exact geometric mesh term.
[GaussianEulerDecayCompactAntiderivative](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayCompactAntiderivative.lean)
identifies the resulting compact decay name with the original
difference of endpoint decay names.
[GaussianSignedRealExponentialOrder](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianSignedRealExponentialOrder.lean)
proves signed real-axis order for the unchanged named exponential.
[GaussianCompactRiemannSplit](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactRiemannSplit.lean)
checks the exact finite split of the actual affine grid at a common step.
[GaussianCompactRiemannAdditivity](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactRiemannAdditivity.lean)
compares the actual shared-step observations via their zero-distance
rate across distinct rational time encodings.
[GaussianPositiveRationalLogarithmSign](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalLogarithmSign.lean)
proves the sign of the original logarithm up to observation error.
[GaussianExponentialRealPartMajorant](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianExponentialRealPartMajorant.lean)
bounds the original complex exponential squared modulus from its actual
real part.
[GaussianEulerDecayOrder](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayOrder.lean)
proves order in the original rational time and binds the actual
nonnegative representative.
[GaussianCompactNamedAdditivity](Lean/IPRADerivations/Analysis/Names/GaussianCompactNamedAdditivity.lean)
proves addition for the original regular compact names, and
[GaussianEulerCompactAdditivity](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactAdditivity.lean)
instantiates it for the unchanged Euler evaluator on positive intervals.
[GaussianEulerHalfDecayQuadrature](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/HalfDecay/GaussianEulerHalfDecayQuadrature.lean)
checks the actual half-argument grid transformation.
[GaussianEulerDecayEndpointBound](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayEndpointBound.lean)
controls the endpoint difference using the left endpoint observation, and
[GaussianEulerHalfDecayTailBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/HalfDecay/GaussianEulerHalfDecayTailBound.lean)
checks the finite upper-cutoff bound for the half-decay kernel.
[GaussianHarmonicLogarithmName](Lean/IPRADerivations/Analysis/Euler/HarmonicLogarithms/GaussianHarmonicLogarithmName.lean)
supplies an exact-order representative of the original logarithm.
[GaussianHarmonicIntegerExponential](Lean/IPRADerivations/Analysis/Euler/HarmonicLogarithms/GaussianHarmonicIntegerExponential.lean)
identifies the actual exponential of its natural multiple with the
exact rational power.
[GaussianEulerUpperPowerCoefficients](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UpperBounds/GaussianEulerUpperPowerCoefficients.lean)
checks the actual doubled real multiplier bound and the nonnegative
harmonic inputs for time at least one.
[GaussianEulerUpperPowerBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UpperBounds/GaussianEulerUpperPowerBound.lean)
proves the bound `t^R+2^-p` at each original power sample.
[GaussianEulerHalfDecayProduct](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/HalfDecay/GaussianEulerHalfDecayProduct.lean)
identifies the original integrand with its power and the two half-decay
factors. [GaussianEulerWeightedHalfDecay](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerWeightedHalfDecay.lean)
checks the factorial majorant of the first product with explicit slack.
[GaussianEulerHalfDecayReference](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/HalfDecay/GaussianEulerHalfDecayReference.lean)
gives the nonnegative scalar representative of the second factor.
[GaussianEulerUpperTailPointwise](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UpperBounds/GaussianEulerUpperTailPointwise.lean)
bounds every original integrand observation at time at least one by
`2^R R!(H_q+2^-q)+2^-p`, where `H_q` is the independent nonnegative
half-decay observation.
[GaussianCompactMeshIndependence](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactMeshIndependence.lean),
[GaussianCompactIntervalRescaling](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactIntervalRescaling.lean)
and [GaussianEulerCompactAlignment](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactAlignment.lean)
identify the original compact Euler names across different legitimate
mesh bounds and rational encodings of the same interval.
[GaussianGammaCompactCutoffGeometry](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaCompactCutoffGeometry.lean)
and [GaussianGammaCompactCutoffAlignment](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaCompactCutoffAlignment.lean)
relate the actual cutoff denominators and align the earlier Euler
quadrature name with the corresponding interval at the later cutoff.
[GaussianGammaCompactCutoffSplit](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaCompactCutoffSplit.lean)
checks the resulting three-piece decomposition of the original
later name, including coincident cutoffs.
[GaussianCompactScalarMajorant](Lean/IPRADerivations/Analysis/RationalArithmetic/Powers/GaussianCompactScalarMajorant.lean)
sums the pointwise scalar majorant on the original grid and passes an
independent row comparison through the actual quadrature weight.
[GaussianEulerCompactUpperTail](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactUpperTail.lean)
proves the upper-cutoff norm bound for the original finite Euler
quadrature using the scaled half-decay kernel and explicit mesh and
observation errors.
[GaussianEulerHalfDecayLeftNorm](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/HalfDecay/GaussianEulerHalfDecayLeftNorm.lean)
retains a bound on the actual left decay observation at arbitrary
rational time. [GaussianEulerUpperTailLeftNorm](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UpperBounds/GaussianEulerUpperTailLeftNorm.lean)
uses it in the original upper-tail grid, with coefficient
`D_R=2^(R+1) R!` and the actual decay observation at `N/4` when
the grid starts at `N/2`. [GaussianEulerNamedUpperTail](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerNamedUpperTail.lean)
removes the auxiliary errors and proves the bound for the original
varying-cutoff upper-tail name.
[GaussianEulerUpperTailCauchyBudget](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UpperBounds/GaussianEulerUpperTailCauchyBudget.lean)
applies the original cutoff height to that estimate.
[GaussianEulerLowerPowerComparison](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerPowerComparison.lean)
checks the signed real upper bound for the actual lower-time power
square. [RationalHarmonicIntervalProduct](Lean/IPRADerivations/Analysis/Series/Harmonic/RationalHarmonicIntervalProduct.lean)
checks the exact product telescope of the original finite harmonic intervals.
[GaussianHarmonicLogarithmPower](Lean/IPRADerivations/Analysis/Euler/HarmonicLogarithms/GaussianHarmonicLogarithmPower.lean)
binds natural powers to the original logarithm. The transformed grid
and the sharp right-endpoint panel bound are checked by
[GaussianEulerLowerTailRootGrid](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTailRootGrid.lean)
and [GaussianEulerLowerTailPowerPanel](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTailPowerPanel.lean).
[GaussianEulerLowerTransformedIntegrand](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTransformedIntegrand.lean)
proves the original pointwise estimate at those transformed times.
[GaussianEulerLowerTailLocalComparison](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTailLocalComparison.lean)
applies the actual sampled modulus to each row of the exact lower
partition and its right endpoint.
[GaussianEulerCompactLowerTail](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactLowerTail.lean)
sums the weighted panel bounds through the exact original grouping.
[GaussianEulerLowerTailFiniteBudget](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTailFiniteBudget.lean)
and [GaussianEulerLowerCofinalQuadrature](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerCofinalQuadrature.lean)
give the cofinal norm bound and approximation to the actual lower name.
[GaussianEulerVaryingCutoffName](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerVaryingCutoffName.lean)
checks the actual varying-cutoff sampler and its regularity from the
lower-tail norm bound.
[GaussianEulerNamedLowerTail](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerNamedLowerTail.lean)
proves that bound on the original lower name at any requested observation
precision under the encoded positive half-plane hypotheses.
[GaussianEulerImproperName](Lean/IPRADerivations/Analysis/Euler/GaussianEulerImproperName.lean)
therefore gives regularity for the unchanged sampler and verifies its
primitive recursive output and evaluation schedule.
[GaussianEulerFixedCutoffApproximation](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerFixedCutoffApproximation.lean)
bounds its distance to the compact name at each fixed cutoff by the sum
of both tail majorants and the two independent observation errors.
[GaussianEulerUnitIntegrand](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitIntegrand.lean)
identifies the exact sample and finite grid at one with the decay program.
[GaussianEulerUnitEndpointDecay](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitEndpointDecay.lean)
bounds the actual endpoint difference at the original cutoffs.
[GaussianEulerImproperNormalization](Lean/IPRADerivations/Analysis/Euler/GaussianEulerImproperNormalization.lean)
proves that the original improper Euler name at the canonical unit
argument agrees with the finite-product Gamma name at arbitrary
independent observation precisions.
[GaussianEulerBetaPoleGuard](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianEulerBetaPoleGuard.lean)
proves the finite weighted Euler operator identity for the actual beta
primitive from the native positive half-plane source.
[GaussianBetaKernelLogarithm](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelLogarithm.lean)
compares the original scaled logarithm with the decay exponent and gives
a fixed compact radius.
[GaussianBetaKernelSignedLogarithm](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelSignedLogarithm.lean)
proves the finite Taylor sign and transfers it to the same original
rounded observation. The real remainder is at least the negative
dyadic allowance and obeys the original quadratic norm bound.
[GaussianBetaKernelDampedDoubling](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelDampedDoubling.lean)
proves the exact one-step relative estimate for the original finite
kernel at degrees `N` and `2N`.
[GaussianBetaKernelDampedRefinement](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelDampedRefinement.lean)
keeps the geometric factor and the actual later kernel throughout
finite dyadic refinement.
[GaussianBetaKernelDecayDampedError](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelDecayDampedError.lean)
bounds the original kernel error by the quadratic factor times the
actual positive decay observation and its explicit allowances.
[GaussianBetaUpperRowDampedError](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaUpperRowDampedError.lean)
keeps the exact high-time row factor `t^(R+2)/N` with the same
positive decay reference and independently queried beta and Euler
observations. [GaussianEulerLowTimePowerOrder](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowTimePowerOrder.lean)
gives the reciprocal-power reference comparison for the actual
lower-time power square.
[GaussianEulerLowTimeReciprocalReference](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowTimeReciprocalReference.lean)
identifies that reference with the exact rational square, and
[GaussianEulerLowTimePowerBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowTimePowerBound.lean)
bounds the original lower-time power norm by `b/a+2^-p`.
[GaussianBetaKernelTailDifference](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaKernelTailDifference.lean)
bounds the absolute full-support kernel difference with one positive
decay factor and explicit observation allowances.
[GaussianBetaRowMonomialReference](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaRowMonomialReference.lean)
compares the actual high-time scalar majorant to the literal monomial
decay evaluator scaled by `1/N`.
[GaussianRationalQuadratureDifference](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianRationalQuadratureDifference.lean)
binds the exact weighted sum of row differences to the original pair
of quadratures.
[GaussianMonomialDecayMajorant](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianMonomialDecayMajorant.lean)
bounds the actual monomial times decay through the weighted half-decay
majorant at coefficient `2^d d!`.
[GaussianMonomialDecayQuadrature](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianMonomialDecayQuadrature.lean)
and [GaussianMonomialDecayBudget](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianMonomialDecayBudget.lean)
retain its integrated coefficient `2^(d+1) d!` above time one with
a computed dyadic allowance.
[GaussianEulerSharpDegreeSchedule](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpDegreeSchedule.lean)
checks the report’s exact choice `N=4(C_R+D_R+p+10)·2^(p+4)`,
the rational bound `C_R/N≤2^(-p-3)`, and the original decay bound at
`N/4` with explicit observation error and a computed precision. The
full integrated sharp comparison remains.
[GaussianBetaLowGridError](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaLowGridError.lean)
proves the exact `1/N` contribution below time one from the actual
beta and Euler row observations, with independently requested errors.
[GaussianBetaUpperGridMonomialComparison](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaUpperGridMonomialComparison.lean)
proves the exact factorial cap divided by the degree for the actual
middle shared grid, with explicit mesh and evaluation allowances.
[GaussianBetaEulerTailDifferencePointwise](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaEulerTailDifferencePointwise.lean)
bounds the actual difference on the upper support by one factorial
half-decay reference and supplies the corresponding scalar majorant.
[GaussianBetaEulerUpperDifferenceGrid](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaEulerUpperDifferenceGrid.lean)
transfers that majorant on the original grid through a single
weighted half-decay quadrature.
[GaussianBetaZeroExtension](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaZeroExtension.lean)
keeps the literal beta evaluator on the support and returns the
canonical zero at the degree and beyond.
[GaussianBetaZeroExtendedGrid](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaZeroExtendedGrid.lean)
checks the finite support and exterior grid identities.
[GaussianCompactAlignedSplit](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactAlignedSplit.lean)
splits a shared mesh using actual equal-time observations, including
zero-width panels.
[GaussianBetaContiguousUpperTail](Lean/IPRADerivations/Analysis/Beta/Tails/GaussianBetaContiguousUpperTail.lean)
uses one factorially weighted original decay observation at a quarter
of the degree for the contiguous upper grid, with explicit sampling
and mesh allowances. The degree may be any fixed natural at least two.
[GaussianEulerSharpFiniteRate](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpFiniteRate.lean)
connects those panels to the original finite Euler reciprocal-inverse
and improper Euler samplers. On the finite sampler domain `1 ≤ R`,
`2R ≤ N`, the checked distance has leading terms
`(1 + 2^(R+3) (R+2)!)/N` and `2^(R+1) R!` times the quarter-degree
decay observation's norm upper bound. That bound uses the exact raw
L1 radius of the original observation plus its own dyadic tolerance.
The finite and improper output clocks are independent and each retains
its own observation tolerance. An explicit finite clock eliminates the
auxiliary mesh and sampling errors inside the object theory.
[GaussianEulerDecayRealSamples](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayRealSamples.lean)
proves that every original decay sample at a rational time is real.
Its raw L1 radius is its exact Euclidean absolute value.
[GaussianEulerSharpGammaRate](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerSharpGammaRate.lean)
transfers the exact radius to the original Gamma observation.
[GaussianEulerSharpScheduledApproximation](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpScheduledApproximation.lean)
uses the stated degree `4(C_R+D_R+p+10)2^(p+4)` and proves that the
original finite observation at `p+2` is within `2^-p` of either
the original improper Euler or Gamma observation at `p+2`.
[GaussianBetaAllDegreeEulerInverse](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaAllDegreeEulerInverse.lean)
certifies the same finite reciprocal evaluator for all positive
degrees, using the height derived from its finite beta endpoint.
Its new data give the same represented value as the previous data
on the original sampler domain.
[GaussianEulerSharpAllDegrees](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpAllDegrees.lean)
proves the sharp rate to the original improper sample for every
`N ≥ 2` on the encoded rational complex half-plane domain, with
independent output and decay precisions.
[GaussianEulerSharpReportTerms](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpReportTerms.lean)
checks that each of the two leading terms is strictly below
`2^-(p+3)` at the stated degree and computed decay query.
[GaussianBetaAllDegreeMixedInverseContinuity](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaAllDegreeMixedInverseContinuity.lean)
proves a cutoff-independent input modulus for the actual all-degree
finite Euler evaluator with separately encoded rational inputs.
[GaussianEulerRealPowerLowerOrder](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerRealPowerLowerOrder.lean)
and [GaussianEulerDecayLowerEnvelope](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayLowerEnvelope.lean)
prove the separate one-half and one-ninth lower estimates on the
original power and decay factors on the interval from one to two.
Each bound retains the tolerance of its actual requested observation.
[GaussianEulerSharpNamedIntegralRate](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpNamedIntegralRate.lean)
extends the sharp rate to general fixed regular complex input names
with a positive real-part margin. It uses the input name's computed
disk radius and keeps the original improper integral observation.
[GaussianEulerSharpNamedSchedule](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/SharpRates/GaussianEulerSharpNamedSchedule.lean)
checks the stated degree for the named Gamma observations.
[GaussianEulerIntegralPositiveLower](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianEulerIntegralPositiveLower.lean)
sums the actual positive unit panel over the common mesh and proves
the bound one eighteenth, with the requested observation tolerance,
for the original improper integral and Gamma at encoded positive real inputs.
[GaussianNamedGammaPositiveLower](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianNamedGammaPositiveLower.lean)
extends it to regular real names with actual real samples and a positive
real-part margin. [GaussianEulerUnitToTopBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitToTopBound.lean)
gives the actual upper panel the factorial bound `2^(R+1) R!` with a
cofinal tolerance. [GaussianEulerEtaToOneRootGrid](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerEtaToOneRootGrid.lean)
checks the actual transformed mesh endpoints and right-row estimate
on the entire panel from the lower cutoff to one.
[GaussianEulerEtaToOneRowBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerEtaToOneRowBound.lean)
compares the original affine rows to those right endpoints.
[GaussianEulerEtaToOneQuadratureBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerEtaToOneQuadratureBound.lean)
sums the original weighted blocks.
[GaussianEulerEtaToOneBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerEtaToOneBound.lean)
gives the corresponding original compact observation radius `A + 2^(-p)`.
[GaussianEulerUnitToTopCompactBound](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitToTopCompactBound.lean)
gives the observation from one the factorial radius with the requested
dyadic tolerance, and compares the actual compact samplers on a fixed
interval with different top guards.
[GaussianEulerIntegralUpperBound](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianEulerIntegralUpperBound.lean)
uses the actual split at one to bound every original cutoff, then
[GaussianEulerIntegralUpperTransfer](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianEulerIntegralUpperTransfer.lean)
gives the original improper and Gamma observation bounds with radius
`A + 2^(R+1) R! + 2^(-p)` for encoded inputs on the positive real
half-plane. The Gamma comparison uses the original guard `1 <= R`.
[GaussianNamedHalfPlaneCorrection](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedHalfPlaneCorrection.lean)
corrects late observations into the exact given half-plane without
changing the computed radius. [GaussianNamedGammaUpperBound](Lean/IPRADerivations/Analysis/Gamma/Names/GaussianNamedGammaUpperBound.lean)
then proves the same radius with the same `A` on regular complex names.
[GaussianEulerUnitNormalizationIntegrand](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitNormalizationIntegrand.lean)
identifies the original unit-argument samples with the decay samples.
[GaussianEulerUnitNormalizationCompact](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitNormalizationCompact.lean)
uses the checked decay antiderivative on the original compact interval.
[GaussianEulerUnitNormalization](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitNormalization.lean)
uses both endpoint bounds to derive the original improper integral value
one and hence the Gamma value one.
[GaussianEulerVerticalProjection](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalProjection.lean)
and [GaussianEulerVerticalNativeProjection](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNativeProjection.lean)
preserve the required disk and positive margin at the real part of the
argument. [GaussianEulerVerticalExponentialSquare](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalExponentialSquare.lean),
[GaussianEulerVerticalExponentReference](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalExponentReference.lean),
and [GaussianEulerVerticalIntegrandSquare](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalIntegrandSquare.lean)
identify the squared norms of the two original integrands.
[GaussianEulerVerticalRealSamples](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalRealSamples.lean)
and [GaussianEulerVerticalRealRadius](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalRealRadius.lean)
give the actual real-axis observations a nonnegative radius with a
dyadic correction. [GaussianPositiveRadiusFiniteSum](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianPositiveRadiusFiniteSum.lean)
and [GaussianPositiveRadiusQuadrature](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianPositiveRadiusQuadrature.lean)
carry certified row bounds through the unchanged finite weighted sums.
[GaussianEulerVerticalNormTransfer](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNormTransfer.lean)
transfers an actual sample radius across the squared norm identity.
[GaussianEulerVerticalPointwise](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalPointwise.lean)
then bounds each original complex row by its original real companion
and four requested dyadic allowances.
[GaussianEulerVerticalQuadrature](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalQuadrature.lean)
gives the actual same-query compact and improper bounds with the precise
grid width and row precision.
[GaussianEulerVerticalShiftedRadius](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalShiftedRadius.lean)
keeps a nonnegative radius when a coarse real observation is signed.
[GaussianEulerVerticalGammaBound](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerVerticalGammaBound.lean)
proves the encoded-input vertical inequality on the original Gamma
observations at independent queries by removing the auxiliary improper
precision. [GaussianEulerVerticalNamedProjection](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNamedProjection.lean)
binds the real projection of a regular name to the decoded native
projection with the original disk.
[GaussianEulerVerticalNamedRadius](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNamedRadius.lean)
and [GaussianEulerVerticalNamedReference](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNamedReference.lean)
compare both actual named Gamma samplers to one late rational input and
its native real projection at a common certified radius.
[GaussianEulerVerticalNamedGammaBound](Lean/IPRADerivations/Analysis/Gamma/Names/GaussianEulerVerticalNamedGammaBound.lean)
gives the same original vertical Gamma inequality at independent queries
of regular complex names, with only the two requested observation allowances.
[GaussianEulerVerticalNamedIntegralBound](Lean/IPRADerivations/Analysis/Euler/VerticalBounds/GaussianEulerVerticalNamedIntegralBound.lean)
proves the same inequality with the original named improper Euler
evaluators and the exact signed comparison radius.
[GaussianEulerIntegrationByPartsLinear](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsLinear.lean)
checks the original time-weighted product's linear term.
[GaussianEulerIntegrationByPartsProductStep](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsProductStep.lean)
and [GaussianEulerIntegrationByPartsStep](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsStep.lean)
give the literal original boundary increment its quadratic cell error
and explicit observation allowance.
[GaussianEulerIntegrationByPartsObservation](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsObservation.lean)
binds the literal power-times-decay product to the actual normalized
integrand at independent queries.
[GaussianEulerIntegrationByPartsGridObservation](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsGridObservation.lean)
carries this comparison to the actual weighted affine grid.
[GaussianEulerIntegrationByPartsEndpoints](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsEndpoints.lean)
bounds the original primitive at the lower cutoff and upper integer time.
[GaussianEulerIntegrationByPartsEndpointRescale](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsEndpointRescale.lean)
compares those times with their actual affine-grid endpoint encodings.
[GaussianEulerIntegrationByPartsGrid](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsGrid.lean)
telescopes the literal finite operator grid and retains an explicit
step and observation error.
[GaussianEulerIntegrationByPartsEndpointBudget](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsEndpointBudget.lean)
bounds each actual affine boundary observation at a computed later cutoff.
[GaussianEulerIntegrationByPartsCofinalGrid](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsCofinalGrid.lean)
chooses a refinement of the original compact mesh and reads the
same grid back to the original compact observations.
[GaussianEulerIntegrationByPartsNormalizedGrid](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsNormalizedGrid.lean)
relates the actual operator grid to the old and shifted normalized
Euler quadratures.
[GaussianEulerIntegrationByPartsRecurrence](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsRecurrence.lean)
combines those estimates with the original Euler-to-Gamma identification
to prove the right-half-plane recurrence on encoded rational inputs,
including the comparison at independent Gamma and product queries.
[GaussianEulerNamedIBPRecurrence](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerNamedIBPRecurrence.lean)
lifts this proof to original regular complex input names, using the
actual normalized translation by one and the original named product.
[GaussianEulerNamedIntegralIBPRecurrence](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerNamedIntegralIBPRecurrence.lean)
gives the corresponding identity of actual improper Euler names.
[GaussianEulerIntegrationByPartsCompact](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsCompact.lean)
keeps both actual shifted-integrand endpoint observations in the
finite compact identity, with a computed error.
[GaussianEulerIncompleteCutoff](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteCutoff.lean)
splits the original later compact name at any positive rational point
on a shared denominator and proves its actual compact additivity.
[GaussianEulerLogarithmicMultiplier](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicMultiplier.lean)
checks the actual logarithmic Euler rows for every numerical order.
[GaussianEulerLogarithmicCompactName](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicCompactName.lean)
constructs their actual regular compact quadrature.
[GaussianUpperTimeLogarithmPower](Lean/IPRADerivations/Analysis/Logarithm/GaussianUpperTimeLogarithmPower.lean)
bounds the original regular logarithmic power on the upper half
of the time axis by the corresponding time power and observation error.
[GaussianEulerIntegrationByPartsCompactNamedIdentity](Lean/IPRADerivations/Analysis/Euler/Integration/Parts/GaussianEulerIntegrationByPartsCompactNamedIdentity.lean)
proves the regular-name compact identity on all encoded positive
intervals, including zero width, retaining both original boundary names.
[GaussianEulerIncompleteCutoffParts](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteCutoffParts.lean)
identifies the change in each actual compact piece at a fixed rational
split with the corresponding original whole-integral tail.
[GaussianEulerIncompleteCutoffRate](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteCutoffRate.lean)
bounds both changes using the original tail coefficients and the two
requested observation precisions.
[GaussianEulerIncompleteName](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteName.lean)
makes the cofinal lower and upper programs into actual regular names,
and [GaussianEulerIncompleteSum](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteSum.lean)
proves that their normalized sum agrees with the actual improper Euler
and Gamma names at every positive rational split.
[GaussianEulerIncompleteFixedCutoff](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteFixedCutoff.lean)
compares the incomplete names to their corresponding compact pieces
at any later fixed cutoff, with the original tail rate.
[GaussianEulerIncompleteRadiusOverlap](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteRadiusOverlap.lean)
aligns physical intervals across two certified radii and proves
agreement of the original names at independent queries.
[GaussianEulerIntegrandTimeProperness](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianEulerIntegrandTimeProperness.lean)
identifies the original shifted integrand at equal rational encodings.
[GaussianEulerIncompleteRecurrence](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteRecurrence.lean)
proves both original incomplete recurrences, retaining the split-point
integrand with opposite signs and bounding the two external terms.
[GaussianEulerIncompleteUnitUpper](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteUnitUpper.lean)
identifies the original upper incomplete sampler at one with decay.
[GaussianEulerIncompleteFactorialDenominator](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteFactorialDenominator.lean)
checks the literal finite factorial polynomial, its original scalar
recurrence, and the integer numerator and denominator.
[GaussianEulerIntegerBoundary](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/Moments/GaussianEulerIntegerBoundary.lean)
identifies the original integer boundary sampler with the literal
rational power times the original decay.
[GaussianEulerIncompleteIntegerFormula](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteIntegerFormula.lean)
derives the upper formula at every internal index by induction on
the fixed-precision numerical error.
[GaussianEulerIncompleteIntegerLowerFormula](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteIntegerLowerFormula.lean)
derives the lower formula from the original sum and factorial value.
[GaussianEulerIncompleteDyadicEndpoint](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteDyadicEndpoint.lean)
uses the original lower-tail bound to prove the exact root rate of
approach to the zero-split values on the original dyadic sequence.
[GaussianEulerIncompleteSmallRationalEndpoint](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteSmallRationalEndpoint.lean)
proves the same uniform bound for every positive rational split at most
the cutoff, with the original lower and upper programs and independent
requested observations.
[GaussianEulerIncompleteZeroModulus](Lean/IPRADerivations/Analysis/Euler/Integration/Incomplete/GaussianEulerIncompleteZeroModulus.lean)
computes a positive rational threshold directly from any requested
endpoint tolerance.
[GaussianLogarithmFactorialPowerBound](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianLogarithmFactorialPowerBound.lean)
derives the literal logarithmic power bound from the corresponding
factorial term of the original finite exponential.
[GaussianEulerLogarithmicHalfDecay](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicHalfDecay.lean)
proves the upper weighted-row bound at the exact factorial majorant
for the combined Euler and logarithmic degree.
[GaussianEulerLowerLogarithmPower](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerLogarithmPower.lean)
proves the inverse-root bound for the actual logarithm at squared root times.
[GaussianEulerLogarithmicUpperPointwise](Lean/IPRADerivations/Analysis/Euler/Logarithms/UpperBounds/GaussianEulerLogarithmicUpperPointwise.lean)
proves the original upper pointwise majorant for the retimed logarithmic compact row.
[GaussianEulerLogarithmicUpperScalar](Lean/IPRADerivations/Analysis/Euler/Logarithms/UpperBounds/GaussianEulerLogarithmicUpperScalar.lean)
supplies the original scalar majorant at the combined degree to the actual compact evaluator.
[GaussianEulerLogarithmicUpperCutoffBudget](Lean/IPRADerivations/Analysis/Euler/Logarithms/UpperBounds/GaussianEulerLogarithmicUpperCutoffBudget.lean)
checks the actual upper logarithmic compact tails at the integer cutoff
with the exact doubled upper factorial coefficient.
[GaussianEulerLogarithmicLowerFiniteBudget](Lean/IPRADerivations/Analysis/Euler/Logarithms/LowerBounds/GaussianEulerLogarithmicLowerFiniteBudget.lean)
checks the actual finite lower logarithmic root quadrature with the
exact factorial coefficient at the doubled root degree.
[GaussianEulerLogarithmicNamedLowerBound](Lean/IPRADerivations/Analysis/Euler/Logarithms/LowerBounds/GaussianEulerLogarithmicNamedLowerBound.lean)
and [GaussianEulerLogarithmicLowerCutoffBudget](Lean/IPRADerivations/Analysis/Euler/Logarithms/LowerBounds/GaussianEulerLogarithmicLowerCutoffBudget.lean)
lift the bound to the actual compact lower name and compute a cutoff
for any requested tail tolerance.
[GaussianEulerLogarithmicIntervalAdditivity](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicIntervalAdditivity.lean)
checks finite additivity at fixed evaluator guards.
[GaussianEulerLogarithmicClientRate](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicClientRate.lean)
proves the original logarithmic rows agree when the evaluator guards change.
[GaussianEulerLogarithmicClientIndependence](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicClientIndependence.lean)
lifts that agreement to the actual compact names.
[GaussianEulerLogarithmicLowerGuardBound](Lean/IPRADerivations/Analysis/Euler/Logarithms/LowerBounds/GaussianEulerLogarithmicLowerGuardBound.lean)
preserves the exact lower coefficient under a larger valid upper-time guard.
[GaussianEulerLogarithmicCommonCutoff](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicCommonCutoff.lean)
identifies the physical cutoff intervals using a computed lower index offset,
with the original integrand radius retained.
[GaussianEulerLogarithmicCertificateGeometry](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicCertificateGeometry.lean)
matches the actual lower endpoints for two independent cutoff certificates.
[GaussianEulerLogarithmicImproperName](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicImproperName.lean)
constructs the actual regular varying-cutoff name at every numerical
logarithmic order.
[GaussianEulerLogarithmicFixedCutoff](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicFixedCutoff.lean)
proves an independent observation rate to any sufficiently late fixed interval.
[GaussianEulerLogarithmicTopExtension](Lean/IPRADerivations/Analysis/Euler/Logarithms/UpperBounds/GaussianEulerLogarithmicTopExtension.lean)
compares an actual compact cutoff with its extension to an arbitrary larger top.
[GaussianEulerLogarithmicCertificateOverlap](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianEulerLogarithmicCertificateOverlap.lean),
[GaussianEulerLogarithmicInputProperness](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicInputProperness.lean),
and [GaussianEulerLogarithmicImproperInputProperness](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicImproperInputProperness.lean)
prove agreement across independent certificates and equal normalized rational inputs.
[GaussianEulerLogarithmicContinuity](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicContinuity.lean)
computes a parameter modulus and proves the independent observation estimate
for the original improper names on certified rational shifts.
[GaussianEulerLogarithmicZeroIdentification](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianEulerLogarithmicZeroIdentification.lean)
identifies the order-zero improper name with the original Gamma program.
[GaussianEulerLogarithmicParameterTaylor](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicParameterTaylor.lean)
checks the actual pointwise first-order remainder at every numerical
order. It derives the shifted radius from the increment bound and
leaves all three original observation queries independent.
[GaussianEulerLogarithmicTaylorGrid](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicTaylorGrid.lean)
integrates the actual quadratic bound on a shared finite grid with
the exact interval-length factor.
[GaussianEulerLogarithmicCompactTaylor](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicCompactTaylor.lean)
lifts the finite estimate to the three independently meshed compact
names and retains the exact quadratic coefficient.
[GaussianEulerLogarithmicCompactParameterRate](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicCompactParameterRate.lean)
derives a fixed-interval parameter Lipschitz estimate from that bound
and the actual compact majorant at the next logarithmic order.
[GaussianEulerDerivativeParameterPath](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeParameterPath.lean)
and [GaussianEulerDerivativeSubdivisionBudget](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeSubdivisionBudget.lean)
verify the native parameter segment, its endpoint and step identities,
and the computed subdivision and relative error budgets.
[GaussianEulerDerivativeSlopeVariation](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeSlopeVariation.lean)
bounds variation of the original improper slopes along the whole path, uniformly
in its subdivision count.
[GaussianEulerLogarithmicPathCompactTaylor](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicPathCompactTaylor.lean)
checks the exact local remainder on successive original compact path observations.
[GaussianEulerDerivativeCommonInterval](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeCommonInterval.lean)
constructs a common physical interval for adjacent orders at every path point
and preserves the independently chosen truncation tolerances.
[GaussianRationalParameterTelescope](Lean/IPRADerivations/Analysis/Series/GaussianRationalParameterTelescope.lean)
sums the finite parameter errors and converts the repeated substep to the actual
whole increment.
[GaussianEulerLogarithmicPathCompactRows](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicPathCompactRows.lean)
and [GaussianEulerDerivativeCompactSlopeRows](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeCompactSlopeRows.lean)
supply the two actual finite row tables.
[GaussianEulerDerivativeEndpointBinding](Lean/IPRADerivations/Analysis/Euler/Derivatives/GaussianEulerDerivativeEndpointBinding.lean)
transports the two compact endpoints to the original improper names.
[GaussianNamedDifferenceQuotient](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNamedDifferenceQuotient.lean)
constructs the actual regular difference quotient for a nonzero native increment.
[GaussianRationalNormalizedTelescope](Lean/IPRADerivations/Analysis/Series/GaussianRationalNormalizedTelescope.lean)
cancels the increment before bounding the finite mean of the slope errors.
[GaussianEulerLogarithmicDerivative](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicDerivative.lean)
proves `I_j' = I_{j+1}` of ledger family 14 on certified native Gaussian
rational inputs for every numerical `j`. Its modulus is independent of the
increment, and the bound is `2⁻ᵖ + 2⁻ᑫ + 2⁻ᵛ` for the independent actual
observations at `q` and `v`.
[GaussianGammaEulerFirstDerivative](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Derivatives/GaussianGammaEulerFirstDerivative.lean)
binds the quotient made directly from the original Gamma evaluator to
the certified order-one logarithmic integral at the same rate.
[GaussianGammaUnitEulerDifference](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Derivatives/GaussianGammaUnitEulerDifference.lean)
gives the explicit positive rational increment schedule at one.
[GaussianRationalUnitInverseExpansion](Lean/IPRADerivations/Analysis/RationalArithmetic/GaussianRationalUnitInverseExpansion.lean)
transports a finite quadratic remainder through inversion using the
actual product residual.
[GaussianGammaDerivativeAtOne](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaDerivativeAtOne.lean)
identifies the original first logarithmic Euler integral at one with
the negative of the original Euler–Mascheroni name. The independent
Gamma difference-quotient observations have the same dyadic derivative
rate for every increment certified by the original Euler derivative
source, including the computed positive rational steps.
[GaussianEulerLogarithmicMixedParameterRate](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianEulerLogarithmicMixedParameterRate.lean)
proves the uniform comparison at distinct native inputs with independent
certificates. [GaussianNamedEulerLogarithmicImproper](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianNamedEulerLogarithmicImproper.lean)
uses a finite demand maximum to construct regular logarithmic improper
evaluators at every numerical order on a fixed certified complex name.
[GaussianRationalQuadratureDilation](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianRationalQuadratureDilation.lean)
checks the finite pullback for a positive rational scale and its exact
Jacobian, preserving the original grid observations.
[GaussianEulerPositiveTimePowerProduct](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/GaussianEulerPositiveTimePowerProduct.lean)
proves the product laws for the original positive-time logarithm and complex power.
[GaussianEulerPositiveScalingIntegrand](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PositiveScaling/GaussianEulerPositiveScalingIntegrand.lean)
proves the actual pointwise pullback identity with modified decay and the
original complex power factor.
[GaussianNamedEulerLogarithmicFrozenRate](Lean/IPRADerivations/Analysis/Euler/Logarithms/Exhaustion/GaussianNamedEulerLogarithmicFrozenRate.lean)
compares the named integral with any sufficiently late decoded input.
[GaussianNamedEulerLogarithmicIncrementBinding](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianNamedEulerLogarithmicIncrementBinding.lean)
uses one decoded base value and its exact Gaussian rational shift.
[GaussianNamedEulerLogarithmicDerivative](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianNamedEulerLogarithmicDerivative.lean)
proves family 14 at every numerical order on any fixed certified regular
complex name, for nonzero native Gaussian rational increments. It preserves
both requested observation precisions and computes the modulus before the
increment is supplied.
[GaussianNamedEulerLogarithmicNamedDerivative](Lean/IPRADerivations/Analysis/Euler/Logarithms/ParameterRates/GaussianNamedEulerLogarithmicNamedDerivative.lean)
extends the same estimate to increments given by regular complex names
with finite apartness and an all-observation smallness certificate. The
actual named reciprocal, original difference, and original named slope
all retain their original query interfaces.
[GaussianNamedEulerLogarithmicZeroIdentification](Lean/IPRADerivations/Analysis/Euler/Logarithms/GaussianNamedEulerLogarithmicZeroIdentification.lean)
proves that the order-zero evaluator agrees with the original Gamma name
on every fixed certified complex input.
[GaussianNamedGammaEulerFirstDerivative](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Derivatives/GaussianNamedGammaEulerFirstDerivative.lean)
proves the first derivative estimate directly for the quotient of the original
named Gamma evaluators along a certified regular named increment.
[GaussianEulerPositiveScalingQuadrature](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PositiveScaling/GaussianEulerPositiveScalingQuadrature.lean)
lifts the scaled integrand identity to the original finite quadrature
with its rational Jacobian and both observation allowances.
[GaussianEulerPositiveScalingCompact](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PositiveScaling/GaussianEulerPositiveScalingCompact.lean)
compares the resulting compact names on a common rational grid.
[GaussianEulerPositiveScalingImproper](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PositiveScaling/GaussianEulerPositiveScalingImproper.lean)
checks family 16 at exponent parameter `r = 1` with a positive rational
damping rate `c / d` and encoded complex input. The compact damped
samples on the inverse-dilated Euler cutoffs form a regular improper
name. Its independent observations agree with the original improper
Euler integral multiplied by the actual inverse scale power
`exp(-(z / B) log(c / d))` within the sum of the two dyadic errors.
[GaussianEulerPositiveScalingGamma](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerPositiveScalingGamma.lean)
identifies the resulting improper name directly with the original
Gamma name times this inverse scale power and proves the forward
identity obtained by multiplying the integral by the positive scale power.
[GaussianRationalQuadratureSquareJacobian](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianRationalQuadratureSquareJacobian.lean)
checks the finite left-endpoint Jacobian error for the quadratic map.
[GaussianEulerSquarePower](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerSquarePower.lean)
checks the original power at a squared rational time against the
original-time evaluator with doubled exponent.
[GaussianEulerSquareIntegrand](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerSquareIntegrand.lean)
identifies the actual Jacobian-weighted Euler observation with the
doubled-power kernel times twice the scale power. It preserves the
finite evaluator and its original product query.
[GaussianRationalQuadratureSquareGridDistance](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianRationalQuadratureSquareGridDistance.lean)
locates the target grid blocks and checks their mapped node distances.
[GaussianEulerQuadraticLowerEndpoint](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerQuadraticLowerEndpoint.lean)
checks cofinal containment and the actual lower omitted-tail bound
at the mapped rational endpoints.
[GaussianEulerSquareCompactComparison](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerSquareCompactComparison.lean)
proves the original compact Euler integral equals the retimed
Jacobian-weighted compact integral on positive-width rational
intervals. It retains both requested observation precisions. The
zero-width finite quadratures both evaluate to zero.
[GaussianEulerQuadraticKernelCompactName](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerQuadraticKernelCompactName.lean)
constructs the regular compact sampler for the unfactored kernel.
[GaussianEulerQuadraticUpperEndpoint](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerQuadraticUpperEndpoint.lean)
aligns a quadratic image endpoint to an original upper cutoff and
bounds the actual omitted upper tail.
[GaussianEulerQuadraticImproperJacobian](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerQuadraticImproperJacobian.lean)
checks the cofinal Jacobian-weighted integral against the original
Gamma evaluator. [GaussianEulerQuadraticImproperKernel](Lean/IPRADerivations/Analysis/Euler/QuadraticSubstitution/GaussianEulerQuadraticImproperKernel.lean)
constructs the separate cofinal sampler for the unfactored kernel
and proves its inverse-factor identity with the original Euler name.
[GaussianEulerQuadraticGamma](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerQuadraticGamma.lean)
checks the quadratic family 15 identity
\(\Gamma(z)=2c^z\int_0^\infty u^{2z-1}e^{-cu^2}\,du\)
for positive rational \(c\) and certified encoded complex \(z\),
with independent observation precisions for the original Gamma
name and the actual factored improper sampler.
[GaussianEulerExponentialSubstitutionNamedKernel](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialSubstitutionNamedKernel.lean)
constructs the actual exponential kernel on a regular input name
and identifies its value at the original logarithm of a positive
rational time. [GaussianEulerExponentialLogGrid](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialLogGrid.lean)
checks the finite logarithmic image sum using the actual widths
and the exponential values at the mapped left endpoints.
[GaussianEulerUnitSubstitutionDensity](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionDensity.lean)
compares the finite original decay-image density to the original
Euler quadrature. [GaussianEulerUnitLogarithmicComposition](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitLogarithmicComposition.lean)
constructs the actual logarithm of minus log at rational inputs
strictly between zero and one.
[GaussianEulerExponentialImproper](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialImproper.lean)
identifies the original Gamma name with the improper sampler of
$e^{zu-e^u}$ on the logarithmic images of the original Euler grids.
[GaussianEulerExponentialLogPartition](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialLogPartition.lean)
proves nonnegative sampled widths, the $C/N$ mesh bound and exact
telescoping. [GaussianEulerExponentialCutoffPartition](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialCutoffPartition.lean)
proves that the actual image endpoints exhaust every fixed signed
interval. [GaussianEulerExponentialNamedKernelRate](Lean/IPRADerivations/Analysis/Euler/ExponentialSubstitution/GaussianEulerExponentialNamedKernelRate.lean)
checks the uniform gain for the genuine kernel on regular names.
[GaussianEulerUnitSubstitutionGamma](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerUnitSubstitutionGamma.lean)
identifies the actual cofinal decay-image density on `u = exp(-t)`
with the original Gamma name. [GaussianEulerUnitSubstitutionImageGrid](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionImageGrid.lean)
checks order, total width and shrinking mesh, and
[GaussianEulerUnitSubstitutionEndpoints](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionEndpoints.lean)
checks exhaustion to zero and one.
[GaussianEulerUnitKernelCompactRate](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelCompactRate.lean)
certifies the genuine rational-input kernel on compact subintervals
of `(0, 1)`.
[GaussianNamedEulerUnitKernel](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianNamedEulerUnitKernel.lean)
extends the actual kernel to regular names whose real samples remain
in the certified compact interval. It derives regularity and
properness from the literal decoded rational samples and their
computed observation precisions.
[GaussianNamedEulerUnitKernelFrozenRate](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianNamedEulerUnitKernelFrozenRate.lean)
compares the actual result with the original rational kernel at any
frozen input sample, with leading error `L / 2^k` and both requested
dyadic allowances.
[GaussianNamedEulerUnitTime](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianNamedEulerUnitTime.lean)
constructs the original harmonic logarithmic time on those inputs.
[GaussianNamedEulerUnitTimeExponential](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianNamedEulerUnitTimeExponential.lean)
recovers the original input by exponentiating the negative of its time.
[GaussianEulerUnitDecayInput](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitTime/GaussianEulerUnitDecayInput.lean)
supplies the exact compact certificate for the original decay at a
computed later precision. For `1/E <= t <= T`, that certificate is
`[1/G, 1-1/G]` with `G = 2(3^T + 4E)`.
[GaussianRealNameExponentialInjectivity](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianRealNameExponentialInjectivity.lean)
derives equality of the original real-axis inputs from equality of
their separately clocked exponentials.
[GaussianNamedEulerUnitKernelAtDecay](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianNamedEulerUnitKernelAtDecay.lean)
proves that the actual time at `u = exp(-t)` equals `t`, and that
the genuine named kernel at that input equals the original Euler
power at `t`, with independent precision allowances. It also bounds
the error of evaluating the rational unit kernel at a literal
rounded decay sample.
[GaussianEulerUnitSubstitutionDensityPrecision](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionDensityPrecision.lean)
gives a uniform bound for independently late observations of the
same fixed-grid density.
[GaussianEulerUnitSubstitutionTiltedNodes](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionTiltedNodes.lean)
gives ordered native rational nodes with an explicit correction of
at most `2N / 2^p` for each original rounded decay node.
[RationalUnitFloorBounds](Lean/IPRADerivations/Analysis/RationalArithmetic/Grids/RationalUnitFloorBounds.lean)
derives compact interval guards for quantized lattice nodes and all
intermediate points. [RationalTiltedFloorWidth](Lean/IPRADerivations/Analysis/RationalArithmetic/Grids/RationalTiltedFloorWidth.lean)
bounds each rounded width by the original signed width, with one
tilt increment and the two floor allowances.
[GaussianEulerUnitSubstitutionReversedWeights](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionReversedWeights.lean)
keeps the original density under exact finite reversal and projects
the actual cell mesh to scalar endpoint distances.
[GaussianEulerUnitKernelCompactName](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelCompactName.lean)
constructs a regular compact unit-kernel quadrature with an explicit
modulus on native rational panels.
[GaussianEulerUnitSubstitutionNearbyKernel](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionNearbyKernel.lean)
bounds the original power against the rational kernel at nearby
points with independent observation precisions.
[GaussianPartitionedFiniteSumTotalDistance](Lean/IPRADerivations/Analysis/Integration/Partitions/GaussianPartitionedFiniteSumTotalDistance.lean)
accumulates the finite row error using the total cut width.
[GaussianPartitionedFiniteSumWeightReplacement](Lean/IPRADerivations/Analysis/Integration/Partitions/GaussianPartitionedFiniteSumWeightReplacement.lean)
controls the replacement of the integer-cell weights by signed widths.
[GaussianEulerUnitSubstitutionFloorCuts](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionFloorCuts.lean)
constructs the absolute and relative integer cuts in a common
certified compact unit interval.
[GaussianEulerUnitSubstitutionLatticeComparison](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionLatticeComparison.lean)
compares the original signed decay-image density to the original
unit kernel evaluated on the resulting uniform rational lattice.
The error includes the original mesh and pointwise rate and the
summed cost of replacing the signed cell widths.
[GaussianEulerUnitSubstitutionLatticeRate](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionLatticeRate.lean)
separates the finite error into the time mesh, decay precision,
lattice denominator and independent kernel precision.
[GaussianEulerUnitSubstitutionIndependentQuadrature](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionIndependentQuadrature.lean)
extends this finite comparison to an independently chosen positive
uniform quadrature count at independent precision on the same
rational panel, including a collapsed rounded panel.
[GaussianEulerUnitSubstitutionPanelComparison](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionPanelComparison.lean)
compares the original regular compact unit quadrature on a computed
rational panel to any independently requested observation of the original
compact Euler name.
[GaussianEulerUnitSubstitutionOrdinaryImproper](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionOrdinaryImproper.lean)
identifies the resulting cofinal ordinary unit quadrature with the original
Gamma name, with independent observation indices. Its Euler comparison
allows any later original time cutoff.
[GaussianEulerUnitSubstitutionOrdinaryEndpoints](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionOrdinaryEndpoints.lean)
proves that the same rounded rational endpoints are strictly inside the
unit interval and approach zero and one with the requested dyadic errors.
[GaussianEulerUnitKernelRationalPanelContinuity](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelRationalPanelContinuity.lean)
bounds the difference of the actual compact unit quadratures on two
panels in a common certified compact interval. Both endpoints may
move by a given rational radius and the two rational denominators
and observation indices may be chosen independently. The leading
error is the endpoint radius times the sum of the compact Lipschitz
constant and twice the kernel majorant.
[GaussianEulerUnitKernelMarginIndependence](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelMarginIndependence.lean)
proves that changing the certified margin on a fixed panel preserves
the original name.
[GaussianEulerUnitSubstitutionOrdinaryContainment](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionOrdinaryContainment.lean)
shows that the actual rounded cofinal panel contains any fixed proper
rational panel as soon as its stage unit reaches that panel's denominator.
[GaussianEulerUnitKernelNestedPanels](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelNestedPanels.lean)
splits the actual compact quadrature on a containing rational panel
into the original contained quadrature and the two omitted strips.
The two original panels can have different denominators and compact
margins, and either strip can have width zero.
[GaussianEulerUnitKernelCompactDominance](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitKernel/GaussianEulerUnitKernelCompactDominance.lean)
bounds the norm of each original compact observation by the real
part of the original quadrature at the projected parameter, plus
both requested observation errors.
[GaussianEulerUnitSubstitutionArbitraryExhaustion](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/UnitSubstitution/GaussianEulerUnitSubstitutionArbitraryExhaustion.lean)
proves the uniform ordinary improper limit for encoded complex inputs
on the certified right half-plane. For target precision `s`, the
denominator of the computed inner reference panel gives a reciprocal
endpoint tolerance. Any proper rational panel within that tolerance
has original compact observation `p` within
`2^(-s) + 2^(-p) + 2^(-q)` of the original Gamma observation `q`.
The proof accepts any valid compact margin. The panel denominator
automatically supplies one for every proper rational panel.
[GaussianEulerPositivePowerChart](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChart.lean)
constructs the actual power chart for positive rational scale and
exponent with compact variation bounds.
[GaussianEulerPositivePowerChartJacobian](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartJacobian.lean)
evaluates the Jacobian of the same chart and bounds the quadratic
increment remainder at independent observation precisions.
[GaussianEulerPositivePowerChartOrder](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartOrder.lean) proves order on rational times with the two independent
dyadic observation allowances. [GaussianEulerPositivePowerChartLogarithm](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartLogarithm.lean) identifies the original
chart with the exponential of its affine logarithmic coordinate.
[GaussianEulerPowerScalingParameter](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingParameter.lean) derives the rescaled native Gamma parameter and
its half-plane source. [GaussianEulerPowerScalingKernel](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingKernel.lean) proves the pointwise kernel
identity including the inverse scale factor and the rescaled complex
exponent. [GaussianEulerPositivePowerChartLower](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartLower.lean) supplies an explicit positive lower bound on
the compact image and exact positive-real sample guards at uniformly
late precisions. [GaussianEulerDampedNamedIntegrand](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDampedNamedIntegrand.lean) identifies the original power-damped Euler
integrand times t with the logarithmic kernel. [GaussianEulerPowerScalingCompactRate](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingCompactRate.lean) gives a
uniform majorant and a compact variation bound for the actual
power-damped integrand. [GaussianEulerPositivePowerChartImage](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartImage.lean) decodes the original retimed chart
samples as exact positive rationals. [GaussianEulerPositivePowerChartMesh](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartMesh.lean) gives ordered corrected
image nodes and a finite mesh bound. [GaussianEulerPositivePowerChartMeshJacobian](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartMeshJacobian.lean) compares individual
corrected widths with the original Jacobian times the physical step and
gives the exact correction on a repeated cell. [GaussianNamedPositiveLogarithm](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianNamedPositiveLogarithm.lean) extends the original
positive-rational logarithm to compact positive names, and [GaussianNamedPositiveLogarithmExponential](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianNamedPositiveLogarithmExponential.lean)
recovers the named input under the original exponential. [GaussianEulerPowerChartNamedLogarithm](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartNamedLogarithm.lean)
identifies the lifted chart logarithm with its affine coordinate.
[GaussianEulerPowerChartFrozenKernel](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartFrozenKernel.lean) gives the compact comparison with the literal time-weighted
Euler row at the frozen decoded image. [GaussianEulerPowerScalingFrozenIntegrand](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingFrozenIntegrand.lean) cancels the
source time and compares the original power-damped integrand directly
to the frozen Euler row with its inverse scale factor. [GaussianEulerPowerScalingCompactName](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingCompactName.lean)
builds the ordinary source-panel quadrature. [GaussianEulerPowerScalingFrozenRow](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingFrozenRow.lean) exposes the exact
original row clocks, and [GaussianEulerPowerScalingCell](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingCell.lean) combines their readback with the
evaluated Jacobian error. [GaussianEulerPowerScalingImageQuadrature](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingImageQuadrature.lean) compares the finite affine source sum
with the corrected image sum and extracts one original scale factor.
[GaussianEulerPositivePowerChartCorrectedImage](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartCorrectedImage.lean) decodes the corrected nodes in a certified compact interval
and compares their original Euler samples to those at the raw image.
[GaussianEulerPowerScalingCorrectedQuadrature](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingCorrectedQuadrature.lean) lifts that comparison to the full finite weighted sum.
[GaussianEulerPowerScalingFiniteSubstitution](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingFiniteSubstitution.lean) combines both finite comparisons with the source-derived
rescaled Gamma parameter and a single common scale observation.
[GaussianEulerPowerScalingFiniteBudget](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingFiniteBudget.lean) separates the mesh and observation errors. [GaussianEulerPowerScalingGridSchedule](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingGridSchedule.lean) gives
an explicit count and two clocks for an arbitrary dyadic accuracy
request. The scheduled source grid refines the unchanged compact
quadrature mesh and gives a comparison to the actual compact name.
[GaussianEulerPositivePowerChartCorrectedPanel](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartCorrectedPanel.lean) proves the corrected nodes lie in their exact rational
endpoint panel and gives a common denominator for the two endpoints.
[GaussianEulerPowerChartRationalPowers](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartRationalPowers.lean) evaluates chart values at native rational powers. [GaussianEulerPowerChartRoundedEndpoints](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartRoundedEndpoints.lean)
controls both actual rounded endpoints. [GaussianEulerPowerChartCofinalSchedule](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartCofinalSchedule.lean) then derives corrected
panels enclosing any prescribed original Euler cutoff while using the
same grid schedule as the finite substitution.
[GaussianEulerPositivePowerChartImageComparison](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPositivePowerChartImageComparison.lean) compares the literal weighted rows to independently counted
ordinary Euler quadratures on the exact corrected panel by refinement
on a common native lattice. [GaussianEulerCompactExhaustion](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactExhaustion.lean) compares arbitrary enclosing
ordinary quadratures to the unchanged improper Gamma name. [GaussianEulerCompactExhaustionScaled](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactExhaustionScaled.lean)
gives a dyadic schedule with the original inverse scale observation,
and [GaussianEulerCompactExhaustionNormalization](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactExhaustionNormalization.lean) supplies the paid-clock cancellation of the chart coefficient.
[GaussianEulerPowerScalingCofinalObservation](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingCofinalObservation.lean) composes the finite substitution and two ordinary image
comparisons with independent observation precisions. [GaussianEulerPowerScalingSourceExhaustion](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingSourceExhaustion.lean) proves
that these physical source panels eventually contain every fixed positive
rational interval. [GaussianEulerPowerScalingImproper](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingImproper.lean) compiles the ordinary panel observations
into the original cofinal improper sampler and derives its equality with
`(1/r) c^(-z/r) Γ(z/r)` for every positive rational `c,r` under the
original encoded right-half-plane assumptions.
[GaussianNamedPositiveReciprocal](Lean/IPRADerivations/Analysis/Names/Apartness/GaussianNamedPositiveReciprocal.lean) gives a regular name by taking exact reciprocals of
literal retimed observations. [GaussianEulerNamedPowerScalingParameter](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingParameter.lean) derives the positive
half-plane margin at the named argument `z/r`, and [GaussianEulerNamedPowerScalingFormula](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingFormula.lean) constructs
the regular Gamma-side product with the original exponential. On
compact intervals, [GaussianNamedDampingPowerChart](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerChart.lean) gives a joint rate in the two parameter
names and the time. [GaussianNamedDampingPowerIntegrand](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerIntegrand.lean) specializes the original named kernel
exactly to constant rational parameters, and [GaussianNamedDampingPowerFrozen](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerFrozen.lean) derives its
uniform pointwise rate to the original kernel at literal decoded
rational parameter observations.
[GaussianNamedDampingPowerCompact](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerCompact.lean) constructs the original compact quadrature name for positive
parameter names. [GaussianNamedDampingPowerCompactPaid](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerCompactPaid.lean) chooses a common freezing clock on each fixed
physical panel, and [GaussianNamedDampingPowerCompactAdditivity](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerCompactAdditivity.lean) checks addition across adjacent panels.
[GaussianNamedDampingPowerCompactBound](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerCompactBound.lean) transfers rational panel bounds with a dyadic allowance. [GaussianEulerNamedPowerScalingGammaFrozen](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerNamedPowerScalingGammaFrozen.lean)
gives the independent rate for the actual Gamma at the named and exact
payload rational arguments. [GaussianEulerPowerChartExponentOrder](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartExponentOrder.lean) orders the rational charts by
exponent on either side of one using their original observations.
[GaussianEulerPowerChartUniformRounded](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartUniformRounded.lean) and [GaussianEulerPowerScalingUniformObservation](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingUniformObservation.lean) choose physical endpoints before either parameter
is frozen, then compare the original enclosing rational quadrature. [GaussianEulerPowerChartUniformExhaustion](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/PowerCharts/GaussianEulerPowerChartUniformExhaustion.lean)
proves cofinality of those physical panels. [GaussianEulerNamedPowerScalingFormulaFrozen](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingFormulaFrozen.lean) gives the independent
rate for the full named Gamma product. [GaussianEulerNamedPowerScalingImproper](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingImproper.lean) identifies the actual
cofinal ordinary quadrature with that product for all certified positive
names. [GaussianNamedDampingPowerLowerCutoff](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerLowerCutoff.lean) gives the independent compact lower-cutoff bound on the
original root grid, including zero width. [GaussianNamedDampingPowerReciprocalTail](Lean/IPRADerivations/Analysis/SpecialFunctions/DampingPower/GaussianNamedDampingPowerReciprocalTail.lean) checks a finite
affine-grid reciprocal-square comparison.
[GaussianEulerNamedPowerScalingExhaustion](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingExhaustion.lean) identifies the exact selected named panel and proves that it
eventually encloses each fixed positive rational interval. [GaussianEulerPowerScalingArbitraryObservation](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingArbitraryObservation.lean)
and [GaussianEulerNamedPowerScalingArbitraryPanel](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingArbitraryPanel.lean) prove the rate for any enclosing positive rational physical
panel with arbitrary independent observation precisions.
[GaussianEulerNamedPowerScalingArbitraryLimit](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingArbitraryLimit.lean) binds the arbitrary enclosing panels directly to the actual
named improper sampler, and [GaussianEulerPowerScalingArbitraryTails](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingArbitraryTails.lean) and [GaussianEulerNamedPowerScalingArbitraryTails](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerNamedPowerScalingArbitraryTails.lean) give the explicit norm
bounds for panels lying wholly outside either physical cutoff.
[GaussianBetaSharpPartition](Lean/IPRADerivations/Analysis/Beta/Partitions/GaussianBetaSharpPartition.lean)
locates one and the two degree endpoints on the same original dyadic
grid and identifies the original half-time decay at the split with
the literal quarter-degree observation.
[GaussianBetaKernelGridComparison](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelGridComparison.lean)
compares the literal finite beta-kernel grid with the original improper
Euler observation at its actual evaluation clock and also allows
independent observation precision on a fixed cutoff interval.
[GaussianEulerBetaProductValue](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianEulerBetaProductValue.lean)
identifies the original reciprocal head with the factorial quotient
of the actual rising product.
[GaussianGammaHalfEulerHead](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfEulerHead.lean) evaluates the original finite head at one half and checks
its exact inverse product. [GaussianGammaHalfEulerExponential](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfEulerExponential.lean) proves that the square of its
original exponential factor is the rational number `1/N` for every
positive finite cutoff.
[GaussianGammaHalfWallisRate](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianGammaHalfWallisRate.lean) gives the finite Wallis rate to the exact arctangent
quadrature. [GaussianGammaHalfSquareLimit](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfSquareLimit.lean) proves that the actual square of the original
half-Gamma name is the arctangent name for pi. [GaussianGammaHalfPositiveRoot](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfPositiveRoot.lean) checks positivity
and the real axis for the same square root. [GaussianGammaHalfSqrtPi](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfSqrtPi.lean)
identifies it with the independently evaluated dyadic square-root program.
[GaussianEulerBetaPrimitivePascal](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianEulerBetaPrimitivePascal.lean)
proves the actual primitive coefficient recurrence at all degrees.
[GaussianEulerBetaEndpoint](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianEulerBetaEndpoint.lean)
identifies the literal primitive at one with the original factorial
quotient for arbitrary internal degree under the native half-plane
guard.
[GaussianPositiveRationalLogarithmIncrement](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalLogarithmIncrement.lean)
checks the original positive-rational logarithm increment with its
quadratic remainder and independent observation errors.
[GaussianBetaKernelDomination](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelDomination.lean)
gives nonnegativity and the original decay upper bound across the
entire finite support.
[GaussianRationalFirstOrderPolynomial](Lean/IPRADerivations/Analysis/Polynomials/Taylor/GaussianRationalFirstOrderPolynomial.lean)
gives the actual beta primitive polynomial increment with a
quadratic residual. [GaussianRationalUniformFirstOrderPolynomial](Lean/IPRADerivations/Analysis/Polynomials/Taylor/GaussianRationalUniformFirstOrderPolynomial.lean)
makes the polynomial estimate uniform on the compact disk.
[GaussianEulerPowerIncrement](Lean/IPRADerivations/Analysis/Euler/Integration/Parameters/GaussianEulerPowerIncrement.lean)
checks the original power increment with the compact quadratic
remainder and the two requested observation errors.
[GaussianBetaPrimitiveCompactStep](Lean/IPRADerivations/Analysis/Beta/Primitives/GaussianBetaPrimitiveCompactStep.lean)
uses the exact synthetic slope and the original power clock to compare
successive primitive samples to the actual weighted beta row.
[GaussianBetaPrimitiveGridTelescope](Lean/IPRADerivations/Analysis/Beta/Primitives/GaussianBetaPrimitiveGridTelescope.lean)
checks the exact finite telescoping and sums that shape of cell error
on the original affine mesh.
[GaussianBetaPrimitiveCompactGridAccuracy](Lean/IPRADerivations/Analysis/Beta/Primitives/GaussianBetaPrimitiveCompactGridAccuracy.lean)
discharges the local conditions from the native compact interval bounds
and computes the mesh and observation precision for any requested
dyadic error.
[GaussianBetaPrimitiveLowerEndpointRefinement](Lean/IPRADerivations/Analysis/Beta/Primitives/GaussianBetaPrimitiveLowerEndpointRefinement.lean)
gives the vanishing degree-scaled lower endpoint at the actual grid
clock. [GaussianBetaUpperEndpointInverse](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaUpperEndpointInverse.lean)
identifies the literal degree-scaled upper endpoint name with the
original finite Euler reciprocal.
[GaussianBetaUpperGridEndpoint](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaUpperGridEndpoint.lean)
makes this comparison for the raw upper grid observation at the
original row clock, with two independent dyadic errors.
[GaussianBetaFiniteEulerComparison](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianBetaFiniteEulerComparison.lean)
compares the unchanged beta quadrature on the whole interval from a
computed lower cutoff to the support endpoint with the original finite
Euler reciprocal at independently requested precisions. The positive
mesh and evaluation precision are computed and may be refined.
[GaussianBetaKernelCompactUpperTail](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelCompactUpperTail.lean)
bounds the original upper beta quadrature through the support endpoint
using the existing half-decay estimates.
[GaussianBetaKernelLowerTransformedPower](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaKernelLowerTransformedPower.lean)
bounds the original lower transformed rows uniformly in the finite
degree.
[GaussianBetaKernelCompactModulus](Lean/IPRADerivations/Analysis/Beta/CompactKernels/GaussianBetaKernelCompactModulus.lean)
proves the compact sampled modulus of that same evaluator uniformly in
the degree.
[GaussianBetaKernelLowerRootQuadrature](Lean/IPRADerivations/Analysis/Beta/Endpoints/GaussianBetaKernelLowerRootQuadrature.lean)
derives the original lower root-grid tail estimate uniformly in the degree.
[GaussianBetaFiniteEulerAtCutoff](Lean/IPRADerivations/Analysis/Beta/EulerProducts/GaussianBetaFiniteEulerAtCutoff.lean)
uses the uniform beta primitive bound to let the lower cutoff be
chosen independently of the degree.
[GaussianBetaFixedCutoffSplit](Lean/IPRADerivations/Analysis/Beta/Partitions/GaussianBetaFixedCutoffSplit.lean)
splits that grid into the actual compact middle and upper tail at the
same step.
[GaussianBetaRefinedFixedCompactBudget](Lean/IPRADerivations/Analysis/Beta/Partitions/GaussianBetaRefinedFixedCompactBudget.lean)
computes the degree and evaluation precision for the actual middle
comparison at any requested dyadic error.
[GaussianEulerIntegralGammaIdentification](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianEulerIntegralGammaIdentification.lean)
proves agreement of the original improper Euler and Gamma names, with
the two independent dyadic observation errors, for an arbitrary encoded
complex rational input on the positive real half-plane.
[GaussianNamedRightHalfPlane](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlane.lean)
derives a native positive margin and a uniform disk for late observations
of a fixed regular input name.
[GaussianGammaHalfPlaneInputContinuity](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaHalfPlaneInputContinuity.lean)
proves a mixed-denominator modulus for the original Gamma observations.
[GaussianNamedGamma](Lean/IPRADerivations/Analysis/Gamma/Names/GaussianNamedGamma.lean)
uses that modulus to derive the regularity of the actual Gamma evaluator
on the fixed input name.
[GaussianNamedEulerIntegrand](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianNamedEulerIntegrand.lean)
proves regularity of the actual integrand at every positive rational time
and agreement with the old integrand for equal encoded rational inputs.
[GaussianEulerIntegrandParameterContinuity](Lean/IPRADerivations/Analysis/Euler/Integration/Parameters/GaussianEulerIntegrandParameterContinuity.lean)
bounds the compact variation between independently encoded rational
parameters at the same time.
[GaussianNamedEulerIntegrandParameterContinuity](Lean/IPRADerivations/Analysis/Euler/Integration/Parameters/GaussianNamedEulerIntegrandParameterContinuity.lean)
carries the compact parameter comparison to a fixed complex name
and its frozen rational observation.
[GaussianNamedEulerCompactTimeRate](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianNamedEulerCompactTimeRate.lean)
derives the compact time rate on the actual named evaluator.
[GaussianNamedEulerQuadrature](Lean/IPRADerivations/Analysis/Euler/GaussianNamedEulerQuadrature.lean)
evaluates that named integrand on the original varying grids with
the certified margin parameter `2A`. Advancing the outer precision by
three gives a regular improper integral name and proves agreement with
the original Gamma program on a fixed regular complex input at arbitrary
independent output precisions.
[GaussianNamedEulerCompactModulus](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianNamedEulerCompactModulus.lean)
constructs the actual regular fixed compact quadrature from the sampled
modulus. [GaussianNamedEulerCutoffBinding](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianNamedEulerCutoffBinding.lean)
identifies each varying-cutoff sample with the corresponding fixed
compact observation at the original clock. The literal C_R/N plus
exponential tail rate of the report remains.

## Every ledger family remains in scope

| Ledger IDs | Complete source deliverables still required |
| --- | --- |
| 1 | Actual harmonic/logarithm Euler-constant evaluator, C1–C2 inequalities, a regular name, and its bounds. |
| 2–3 | Actual cofinal samplers establish C11 for the literal Weierstrass product and C15 for the Euler reciprocals. The C7 and Gamma names agree on overlapping disks for the same encoded rational point. The right-half-plane Euler integral agrees with the original Gamma name on encoded complex rational inputs. The Gamma evaluator and fixed-time Euler integrand now extend to regular fixed complex names. The original improper Euler quadrature on a fixed regular complex name agrees with its Gamma name. |
| 4–10 | The original C7 zero predicate is characterized by an exact pole search for encoded rational inputs. The actual Gamma observations have a quantitative nonvanishing bound on pole-free disks. The whole finite coefficient product has the C9 majorant and the radius-doubled degree tail. C23 and C25 have checked difference-quotient and residue limits on encoded rational increments. The original cofinal coefficient names and C19 are checked on encoded disks. Entire analyticity and classification for general named inputs remain. C20, the original C21 shift and factorial values, C22, and the C24 punctured-disk identity are proved on their recorded domains. C26 conjugation and the real value representation for encoded real rational inputs are proved for the original reciprocal and pole-free Gamma names. |
| 11–17 | [GaussianGammaIntegralCutoffs](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaIntegralCutoffs.lean) checks the numerical endpoints and budgets for the original mesh. [GaussianPositiveRationalLogarithm](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalLogarithm.lean) constructs the positive-rational logarithm and checks its exponential. [GaussianPositiveExponentialTermBound](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianPositiveExponentialTermBound.lean) checks the finite factorial-term lower bound used in the upper integral tail. [GaussianEulerIntegrandName](Lean/IPRADerivations/Analysis/Euler/Integration/GaussianEulerIntegrandName.lean) constructs the actual regular sampled integrand. [GaussianRationalRiemannRefinement](Lean/IPRADerivations/Analysis/Integration/GaussianRationalRiemannRefinement.lean) proves the weighted finite refinement bound from the original cell distances. [GaussianPositiveRationalExponentialDecay](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianPositiveRationalExponentialDecay.lean) proves the factorial monomial bound for the named negative exponential with explicit dyadic observation slack. [GaussianEulerDecayFactorBounds](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayFactorBounds.lean) transfers the dyadic integer and weighted half-argument bounds to the actual decay program. [GaussianGammaIntegralTailBudget](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaIntegralTailBudget.lean) checks the exact left root and the combined endpoint majorant at the prescribed cutoffs. [RationalHarmonicInterval](Lean/IPRADerivations/Analysis/Series/Harmonic/RationalHarmonicInterval.lean) proves the exact signed harmonic-interval refinement and equal-ratio estimates. [GaussianExponentialLinearRemainder](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianExponentialLinearRemainder.lean) checks the original exponential linear remainder on the unit disk. [GaussianPositiveRationalLogarithmProperness](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalLogarithmProperness.lean) proves agreement of the original logarithm across equal positive rational encodings. [GaussianGammaRightHalfPlane](Lean/IPRADerivations/Analysis/Gamma/GaussianGammaRightHalfPlane.lean) derives the original Gamma domain and C15 rate from the positive real-part margin. [RationalHarmonicIntervalVariation](Lean/IPRADerivations/Analysis/Series/Harmonic/RationalHarmonicIntervalVariation.lean) gives the finite harmonic variation bound and [GaussianNamedLipschitzRate](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedLipschitzRate.lean) removes auxiliary dyadic errors from diagonal estimates of regular names. [GaussianCompactRiemannName](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactRiemannName.lean) derives regular compact quadrature from an actual local sampled modulus. [GaussianGammaCompactQuadratureBoundary](Lean/IPRADerivations/Analysis/Gamma/Integrals/GaussianGammaCompactQuadratureBoundary.lean) binds that construction to the Gamma cutoffs on each fixed interval. [GaussianEulerDecayAddition](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayAddition.lean) checks addition of rational decay arguments and the linear remainder for the original decay samples. [GaussianPositiveRationalLogarithmVariation](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalLogarithmVariation.lean) proves the original logarithm variation rate. [GaussianRationalUniformExponentialLipschitz](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianRationalUniformExponentialLipschitz.lean) gives a uniform variation bound for the original finite scalar exponential on a disk. [GaussianEulerDecayIncrement](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayIncrement.lean) establishes a uniform first-order remainder for the original positive-time decay samples. [GaussianEulerDecayMesh](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayMesh.lean) sums this error on an actual finite mesh and compares to the endpoint difference. [GaussianEulerDecayQuadrature](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayQuadrature.lean) compares the actual affine-grid decay sum to the two original endpoint observations with a quantitative error. [GaussianCompactLogarithmBounds](Lean/IPRADerivations/Analysis/Logarithm/GaussianCompactLogarithmBounds.lean) bounds the actual compact logarithm observations uniformly. [GaussianRadiusExponentialLipschitzRate](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianRadiusExponentialLipschitzRate.lean) lifts the finite variation bound to the original exponential names. [GaussianPositiveExponentialOrder](Lean/IPRADerivations/Analysis/Exponential/PositiveAxis/GaussianPositiveExponentialOrder.lean) checks finite positive-axis order and [GaussianExponentialRealPart](Lean/IPRADerivations/Analysis/Exponential/GaussianExponentialRealPart.lean) relates the exponential norm square to the real part of its exponent. The [checked Euler quadrature](#checked-euler-quadrature) now supplies the original integrand modulus, regular varying-endpoint improper quadrature, and its comparison to each fixed compact name with both endpoint majorants. The Euler-integral identification is checked on encoded rationals and fixed regular complex names. The sharp finite Euler rate is checked for every degree at least two on encoded complex inputs. The stated degree schedule gives the evaluated original observation corollaries. The sharp finite-sampler rate extends to general regular complex names at the computed radius. The one-eighteenth lower bound is checked for encoded positive real inputs and regular positive real names with actual real samples. The combined factorial upper bound is checked on encoded inputs and regular names at their computed radii. The decay antiderivative gives a checked integral proof of the Gamma value at one. The vertical integrand squared norm identity is checked. The vertical Gamma comparison is checked for encoded inputs and regular complex names. Integration by parts gives the recurrence on encoded rational inputs and regular complex names. The compact logarithmic quadratures, incomplete-Gamma sum and both recurrences are checked on encoded rational inputs with positive rational split. The upper and lower integer formulas are checked for all numerical indices at positive rational splits. Every positive rational split at most the original cutoff has the exact root rate to the zero-split values. The all-order derivative of the logarithmic integral names (family 14) is checked on certified native Gaussian rationals and fixed regular complex input names, including named increments with finite apartness and all-observation smallness. The finite Euler scaling comparison includes the exact Jacobian. Its cofinal lift proves the improper scaling law at exponent parameter one for positive rational damping and encoded complex input, including the direct original Gamma identity. The quadratic map has checked finite Jacobian and complex-power identities, actual pointwise integrand transport, compact Jacobian-weighted integration on positive-width rational intervals, and both omitted tails. Its cofinal lift proves the quadratic improper identity with the original Gamma evaluator for positive rational damping and encoded complex input. The exponential improper form is checked on the actual ordered logarithmic image partitions with explicit cofinal endpoint bounds. The unit-interval decay-image sampler is checked against the original Gamma evaluator, with explicit endpoint exhaustion and shrinking mesh. The genuine unit kernel has a uniform compact rate, a checked extension to regular compact real input names, and a checked pointwise pullback to the original Euler power at every certified decay-image input. The finite density is compared with independently counted uniform quadratures on the rounded rational panels. The original Gamma name is identified with the cofinal ordinary quadrature on the computed rational unit panels, with an independently later original time cutoff and explicit endpoint exhaustion. Compact endpoint continuity holds at independent rational denominators and observation indices, and arbitrary fixed proper rational panels are eventually contained in the computed cofinal panels. Exact nested panel splitting and compact real-parameter domination are checked at independent observation indices. A uniform omitted-tail bound identifies arbitrary proper rational endpoint exhaustions with the original Gamma name for encoded complex inputs, with independent observation queries. [GaussianEulerPowerScalingImproper](Lean/IPRADerivations/Analysis/Euler/PowerScaling/GaussianEulerPowerScalingImproper.lean) proves the original improper power-damping identity for positive rational damping and exponent and encoded complex input. The extension to arbitrary positive real scaling remains open. |
| 18–24 | Reflection with an explicit sine margin, multiplication at arbitrary internal positive integer multiplier, duplication/triplication, beta–Gamma relation, beta symmetry/recurrence and all stated integral forms with their positive half-plane margins. [GaussianScalarExponentialOddTaylor](Lean/IPRADerivations/Analysis/Exponential/FiniteSeries/GaussianScalarExponentialOddTaylor.lean), [GaussianScalarSineTaylor](Lean/IPRADerivations/Analysis/Trigonometry/GaussianScalarSineTaylor.lean), and [GaussianNamedSineTaylor](Lean/IPRADerivations/Analysis/Trigonometry/GaussianNamedSineTaylor.lean) give the finite and named sine series identities used in the trigonometric foundation. [GaussianArctangentCayleyRefinement](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyRefinement.lean) proves the explicit finite Cayley estimate at any rational arctangent endpoint in the unit interval. [GaussianArctangentPartialQuadrature](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentPartialQuadrature.lean) gives the regular native partial arctangent, [GaussianArctangentPartialRepresentation](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentPartialRepresentation.lean) removes dependence on the fraction encoding, and [GaussianArctangentPartialUnitEndpoint](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentPartialUnitEndpoint.lean) matches the unit endpoint with the original π program. [GaussianArctangentPartialExponential](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentPartialExponential.lean) and [GaussianArctangentPartialTrig](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentPartialTrig.lean) prove the named exponential, sine and cosine identities in T1 at every encoded rational arctangent parameter in the unit interval. [GaussianArctangentChordComparison](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentChordComparison.lean) and [GaussianArctangentNamedChord](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentNamedChord.lean) give the finite and independently sampled T2 chord comparison on the rational arctangent image. [GaussianArctangentSlope](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentSlope.lean) proves the finite lower and upper slope bounds, and [GaussianArctangentGridSearch](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentGridSearch.lean) finds the first row crossing a target with an explicit residual. [GaussianArctangentNamedSlope](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentNamedSlope.lean) lifts the two slope bounds to the original names at independent precisions. [GaussianArctangentRationalTarget](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentRationalTarget.lean) clears rational target denominators exactly and bounds the selected observation by `2/M` from the target when it is in the finite grid range. [GaussianArctangentClampedTarget](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentClampedTarget.lean) proves the native prefix is independent of the clearing factorial and verifies clipping to the endpoints for finite nonnegative inverse targets. [GaussianArctangentPhysicalRefinement](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentPhysicalRefinement.lean) retains the actual mesh denominator in the forward error and compares any selected inverse sample to the original named arctangent at the selected rational parameter. [GaussianArctangentInverseSampler](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentInverseSampler.lean) and [GaussianArctangentInverseForward](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentInverseForward.lean) implement the inverse sampler for arbitrary regular angles certified by the independent-precision interval inequalities, with forward error at most `7/2^p` on the selected finite grid. [GaussianArctangentInverseGap](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentInverseGap.lean) transfers forward errors to rational parameter errors. [GaussianArctangentNamedInverse](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentNamedInverse.lean) proves regularity and exact rational readback for the inverse. [GaussianArctangentInverseUniqueness](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentInverseUniqueness.lean) proves equivalence for inverse names of equivalent target angles, and [GaussianImaginaryCoordinateName](Lean/IPRADerivations/Analysis/Names/ImaginaryParts/GaussianImaginaryCoordinateName.lean) checks the regular coordinate name used to state the inverse identity. [GaussianArctangentNamedExtension](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Extension/GaussianArctangentNamedExtension.lean) defines the regular forward name and [GaussianArctangentExtensionRange](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Extension/GaussianArctangentExtensionRange.lean) certifies its target interval. [GaussianArctangentInverseCorrectness](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Inverse/GaussianArctangentInverseCorrectness.lean) identifies the angle coordinate after forward evaluation of the inverse and gives full Gaussian name equivalence for imaginary-axis angle samples. [GaussianArctangentNamedExtensionUniqueness](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Extension/GaussianArctangentNamedExtensionUniqueness.lean) recovers exactly represented unit-interval parameter names after the opposite round trip. [GaussianArctangentNamedCayley](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentNamedCayley.lean) identifies the original named exponential of the general forward program with regular observations of the literal Cayley quotient. [GaussianArctangentNamedCayleyTrig](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentNamedCayleyTrig.lean) identifies both original sine and cosine names with literal Cayley formulas on regular parameters. [GaussianArctangentNamedChordExtension](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Extension/GaussianArctangentNamedChordExtension.lean) proves the sampled chord for the general forward name, and [GaussianArctangentAngleChord](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentAngleChord.lean) transfers it through the exact inverse to every certified imaginary-axis angle in the original interval. [GaussianArctangentPiMargins](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentPiMargins.lean) proves the margins 1501/500 ≤ π ≤ 7/2 with the observation error. For T3, [GaussianScalarSincTaylor](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianScalarSincTaylor.lean) proves the literal finite sine–sinc identity at all inputs, [GaussianScalarSincTaylorBounds](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianScalarSincTaylorBounds.lean) gives the quadratic error on the unit disk, and [GaussianSineMultipleAngleRecurrence](Lean/IPRADerivations/Analysis/Trigonometry/MultipleAngles/GaussianSineMultipleAngleRecurrence.lean) proves the zero-safe multiple-angle difference law and even recurrence. [GaussianNamedSinc](Lean/IPRADerivations/Analysis/Trigonometry/GaussianNamedSinc.lean) constructs the regular factorial sinc name on bounded inputs and [GaussianNamedSineSincFactorization](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianNamedSineSincFactorization.lean) proves its division-free identity with the original named sine. [GaussianSineSquaredPolynomial](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSquaredPolynomial.lean) gives the actual monic multiple-angle polynomial; [GaussianSineSquaredTrace](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSquaredTrace.lean) evaluates it at the squared-sine coordinate and proves the rational power-difference root implication; [GaussianSineSquaredNormalization](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSquaredNormalization.lean) evaluates it at zero sine. [GaussianArctangentDivisionAngles](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionAngles.lean) certifies the divided angles, and [GaussianArctangentDivisionAngleRoots](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionAngleRoots.lean) proves the original sine vanishes after multiplication by the odd order. [GaussianArctangentDivisionAngleGaps](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionAngleGaps.lean) proves the uniform synchronized gaps between the angle observations and from the quarter endpoint. [GaussianRationalSeparatedDeflation](Lean/IPRADerivations/Analysis/Polynomials/RootFinding/Deflation/GaussianRationalSeparatedDeflation.lean) propagates residual bounds through rational synthetic deflation, and [GaussianRationalSeparatedReconstruction](Lean/IPRADerivations/Analysis/RationalArithmetic/Representations/GaussianRationalSeparatedReconstruction.lean) bounds the resulting product evaluation error at separated samples. [GaussianArctangentDivisionSinePositive](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionSinePositive.lean) proves the actual sine at each positive prescribed angle is at least 2k/m. [GaussianNamedSincQuadraticBounds](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianNamedSincQuadraticBounds.lean) and [GaussianNamedSincRatio](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianNamedSincRatio.lean) give the original named sinc quadratic and squared-ratio estimates. [GaussianInverseSquareProductTail](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianInverseSquareProductTail.lean) proves an explicit finite inverse-square product tail and [GaussianSineProductName](Lean/IPRADerivations/Analysis/Trigonometry/GaussianSineProductName.lean) gives a regular name for the literal product. [GaussianSineProductT4Budget](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductT4Budget.lean) checks the numerical T4 clock and closes the final error absorption under its product and prefactor estimates. For R1, [GaussianGammaEulerReflectionHead](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaEulerReflectionHead.lean) pairs the original heads and [GaussianGammaEulerReflectionName](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaEulerReflectionName.lean) proves the exact reflection value of the original finite Euler approximant names on the certified pole-free domain. [GaussianGammaEulerReflectionLimit](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaEulerReflectionLimit.lean) passes the finite identity to the original reciprocal Gamma names at independent output precisions. [GaussianGammaReflectionProduct](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaReflectionProduct.lean) proves the limiting reflection product for the original Gamma names at $z$ and $1-z$, with constructive division by $zS(z)$ on the certified pole-free domain. [GaussianGammaReflectionSineTransfer](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaReflectionSineTransfer.lean) derives the original cleared sine reflection formula from T7 at the original argument. [GaussianInverseSquareProductGrowth](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianInverseSquareProductGrowth.lean) checks the uniform inverse-square product envelope, [GaussianArctangentCayleySquareGap](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleySquareGap.lean) gives the finite Cayley square gap, and [GaussianSineSquaredResidual](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSquaredResidual.lean) converts the power discrepancy into a quantitative polynomial residual. [GaussianArctangentDivisionAngleResidual](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionAngleResidual.lean) bounds the residual at the actual rational Cayley observations given a sampled sine margin. [GaussianInverseSquareProductComparison](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianInverseSquareProductComparison.lean) bounds the weighted difference of the actual finite products. [GaussianSineSampleRootList](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSampleRootList.lean) instantiates the finite monic reconstruction bound with the original rational root samples under explicit separation. [GaussianArctangentDivisionCayleyMargins](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionCayleyMargins.lean) proves the sampled sine lower bounds and pairwise squared-sine separation on the actual inverse grid. [GaussianSineProductT6](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductT6.lean) combines the finite head, suffix, and sinc prefactor estimates to the exact T4 radius, and [GaussianSineProductT4Finite](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductT4Finite.lean) closes the finite quantified estimate and dyadic precision form. [GaussianSincRatioProductRow](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianSincRatioProductRow.lean) derives the head and prefactor estimates from certified sinc observations. [GaussianSineRootNormalization](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineRootNormalization.lean) identifies each normalized linear root factor with $1-s^2/r^2$ under its proved sine margin. [GaussianSineSampleRootGuards](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSampleRootGuards.lean) applies the exact rational root margin and residual estimates to the actual polynomial and its finite root list. [GaussianSineSquaredRootSeparation](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineSquaredRootSeparation.lean) applies the exact rational root margin and residual estimates to the actual polynomial and its finite root list. [GaussianArctangentDivisionSineSeparation](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/DivisionAngles/GaussianArctangentDivisionSineSeparation.lean) transfers the gap to the original squared sine names at independent precisions, and [GaussianSineProductScaledArguments](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductScaledArguments.lean) checks the actual T4 scaled arguments and their sinc radius guards. [GaussianSineNormalizedSampleProduct](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineNormalizedSampleProduct.lean) proves the exact normalized finite factor fold, and [GaussianSineNormalizedSampleReconstruction](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineNormalizedSampleReconstruction.lean) gives an explicit cofinal error against the multiple-angle polynomial divided by the odd order. [GaussianNamedSineMultipleAngle](Lean/IPRADerivations/Analysis/Trigonometry/MultipleAngles/GaussianNamedSineMultipleAngle.lean) proves the named multiple-angle sine identity on every bounded Gaussian input, and [GaussianNamedEvenSinePolynomial](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianNamedEvenSinePolynomial.lean) identifies its even recurrence with the odd order times the normalized polynomial. [GaussianSineNormalizedSampleName](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineNormalizedSampleName.lean) identifies the normalized polynomial with the regular root-product name. [GaussianSineNormalizedForwardProduct](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineNormalizedForwardProduct.lean) verifies the ascending rational factor order. [GaussianSineProductScaledArgumentIdentity](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductScaledArgumentIdentity.lean) and [GaussianSineProductRelativeArgument](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductRelativeArgument.lean) bind the original scaled arguments and root sine to the literal arithmetic. For R3, [GaussianSineProductHeadLower](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductHeadLower.lean) and [GaussianSineProductTailLower](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductTailLower.lean) prove the factorial head and inverse-square tail bounds, [GaussianSineProductReflectionLower](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductReflectionLower.lean) transfers their exact product to the original name, and [GaussianSineReflectionLower](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineReflectionLower.lean) proves the original sine lower bound at an explicit dyadic reserve given the T7 identity. [GaussianNamedSincCongruence](Lean/IPRADerivations/Analysis/Trigonometry/Sinc/GaussianNamedSincCongruence.lean) transports sinc across independently certified equivalent names. [GaussianSineProductNamedT3](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductNamedT3.lean) proves T3 at the original reflection argument, with explicit cancellation for nonzero numerators and exact zero-sample identities at zero. [GaussianSineRawRootBinding](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineRawRootBinding.lean) and [GaussianSineProductSynchronizedRow](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductSynchronizedRow.lean) identify the original Cayley observations and bound each actual normalized factor at a synchronized query clock. [GaussianSineProductSynchronizedMagnitude](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductSynchronizedMagnitude.lean) verifies the inverse-square envelope on all actual Cayley rows. [GaussianSineProductT4Actual](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductT4Actual.lean) proves the synchronized comparisons at the common cofinal clock, and [GaussianSineProductT7Actual](Lean/IPRADerivations/Analysis/Trigonometry/SineProducts/GaussianSineProductT7Actual.lean) proves the T7 identity for the original sinc, the exact R3 bound at every certified precision, and both cleared and divided Gamma reflection (claim 18). The ordinary quotient uses [GaussianGammaReflectionQuotient](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaReflectionQuotient.lean) and [GaussianGammaReflectionR3Domain](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Reflection/GaussianGammaReflectionR3Domain.lean) to compute the sine reciprocal from the original complementary pole guards. For Gauss multiplication, [GaussianRationalRectangularProduct](Lean/IPRADerivations/Analysis/RationalArithmetic/FiniteProducts/GaussianRationalRectangularProduct.lean), [GaussianGammaEulerDenominator](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/GaussianGammaEulerDenominator.lean), and [GaussianGammaEulerDenominatorGrouping](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerDenominatorGrouping.lean) prove the finite denominator grouping in M2 at arbitrary positive integer multiplier. [GaussianGammaGaussEulerHeads](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGammaGaussEulerHeads.lean) identifies the grouped product of the actual shifted Euler heads with the factorial-normalized head at the Gauss cutoff. [GaussianGammaGaussDomain](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGammaGaussDomain.lean) pulls the original scaled pole guard back to every shifted argument. [GaussianGammaGaussReference](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/ReferenceProduct/GaussianGammaGaussReference.lean) certifies the positive normalization arguments and computes the common exponent offsets. For M1, [GaussianCyclicExponentialRoots](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicExponentialRoots.lean) proves the original cyclic root law and [GaussianCyclicExponentialSeparation](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicExponentialSeparation.lean) supplies separated actual observations. For M3, [GaussianGaussMultiplicationLogarithm](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/PowerEstimates/GaussianGaussMultiplicationLogarithm.lean) proves the exact $1/N$ bound on the original integer logarithm samples and gives an independent-clock version. [GaussianNamedFiniteProductName](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteProductName.lean) lifts rowwise approximations to the regular name of their finite product. [GaussianCyclicRootProduct](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicRootProduct.lean) reconstructs the finite cofinal product of the nontrivial cyclic factors at one. [GaussianGaussEulerHeadCancellation](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerHeadCancellation.lean) cancels the common factorial factors across two original Euler head products, and [GaussianGaussEulerRowExponents](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerRowExponents.lean) identifies the common exponential factor for every shifted row. [GaussianGaussMultiplicationLogRatio](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/PowerEstimates/GaussianGaussMultiplicationLogRatio.lean) proves the corresponding rate for the original positive rational log names at bases $N/L$ and $1/m$. [GaussianNamedFiniteProductApartness](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteProductApartness.lean) gives explicit reciprocal clocks for regular finite products with a uniform row margin, including the exact empty product. [GaussianGaussMultiplicationSharpPowerRate](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/PowerEstimates/GaussianGaussMultiplicationSharpPowerRate.lean) proves M3 with exact leading coefficient $2A m^A$, where $A=m(R+1)$, and the independent observation errors. [GaussianGaussEulerCutoff](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerCutoff.lean) computes the common Euler cutoff and proves that each larger cutoff also gives the required error. [GaussianGammaGaussShiftedProduct](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGammaGaussShiftedProduct.lean), [GaussianGammaGaussShiftedApartness](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGammaGaussShiftedApartness.lean), and [GaussianGammaGaussEulerProduct](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGammaGaussEulerProduct.lean) construct the original shifted Gamma product, certify its reciprocal clock, and prove convergence of the literal finite Euler product. [GaussianNamedFiniteProductAlgebra](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteProductAlgebra.lean) and [GaussianNamedRepeatedExponential](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedRepeatedExponential.lean) transport finite rowwise multiplication and repeated exponentials through the actual clocks. [GaussianCyclicChordSquare](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicChordSquare.lean) and [GaussianCyclicSineProductSquare](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicSineProductSquare.lean) identify the cyclic chord product with the squared sine product at certified clocks. [GaussianCyclicSinePositiveRows](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicSinePositiveRows.lean) and [GaussianCyclicSineProductNormalization](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicSineProductNormalization.lean) justify cancellation of the square on the actual finite rows. [GaussianCyclicSineProductName](Lean/IPRADerivations/Analysis/Trigonometry/Cyclic/GaussianCyclicSineProductName.lean) proves M1 for the primitive recursive product of the original sine names at arbitrary positive internal order, with value $m/2^{m-1}$. [GaussianGaussEulerPowerRatio](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerPowerRatio.lean) proves the exact ratio-power law at the two original cutoff logarithms, and [GaussianGaussEulerOffsetPower](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerOffsetPower.lean) collects the repeated relative factors into the exponential of the scaled coefficient. [GaussianGammaEulerFullHeadInverse](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/FiniteHeads/GaussianGammaEulerFullHeadInverse.lean) factors each actual Euler name through its complete head reciprocal. [GaussianNamedFiniteProductFamilyCongruence](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteProductFamilyCongruence.lean) transports regular families of independently sampled rows to their actual product names. [GaussianGammaGaussReferenceProduct](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/ReferenceProduct/GaussianGammaGaussReferenceProduct.lean), [GaussianGammaGaussReferenceEulerProduct](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/ReferenceProduct/GaussianGammaGaussReferenceEulerProduct.lean), and [GaussianGaussMultiplicationCofinalRows](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGaussMultiplicationCofinalRows.lean) construct the reference product with a reciprocal clock and bind the shifted, reference, scaled, and ratio observations to their limiting names at one padded cutoff. [GaussianGaussMultiplicationM2Transport](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGaussMultiplicationM2Transport.lean) proves M4 in its cleared form from the exact named M2 identity at the cofinal Euler cutoffs. It constructs the named finite factors and uses uniform observation bounds to pass to the original Gamma names. [GaussianGaussEulerFiniteIdentity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerFiniteIdentity.lean) proves exact cleared M2 on the original finite Euler names and passes to the cleared Gamma limit at the cofinal cutoffs. [GaussianGammaGaussReferenceSquare](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/ReferenceProduct/GaussianGammaGaussReferenceSquare.lean) proves the exact squared M5 normalization $P_m^2=(2\pi)^{m-1}/m$ for the original reference product, by the actual reflection rows and M1. [GaussianGammaGaussPositiveReference](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/ReferenceProduct/GaussianGammaGaussPositiveReference.lean) gives a primitive recursive representative of the certified positive root and proves its real positivity and exact square. [GaussianGaussMultiplication](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGaussMultiplication.lean) proves the divided M4 formula with the actual scaled Gamma reciprocal and the M5 formula in the form $m^{1-mz}\sqrt{(2\pi)^{m-1}/m}\,\Gamma(mz)$ for every positive internal order. The normalized formula uses the certified positive-root representative from the reference rows. [GaussianGaussMultiplicationIndependentNormalization](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/Normalization/GaussianGaussMultiplicationIndependentNormalization.lean) also computes that root directly from the radicand. [GaussianGaussEulerRelativeQuotient](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Gauss/GaussianGaussEulerRelativeQuotient.lean) proves the literal M2 nested quotient at every certified cutoff. [GaussianGaussMultiplicationHalfPowers](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/Normalization/GaussianGaussMultiplicationHalfPowers.lean) proves the displayed M5 identity with separately computed $(2\pi)^{(m-1)/2}$ and $m^{1/2-mz}$. [GaussianGaussDuplication](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGaussDuplication.lean) and [GaussianGaussTriplication](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/Multiplication/GaussianGaussTriplication.lean) prove M6 and M7 for the explicit original Gamma rows at their common denominators. |
| 25–30 | Positive-root selection and half-integer values, the listed fractional-argument relations and fractional products, and imaginary/half-shifted modulus formulas, including their zero-safe versions. V8 and V9 hold for the original Gamma names on certified endpoints at arbitrary internal indices. The entire cleared V9 identity covers apparent cancelled poles. |
| 31–36 | Digamma and polygamma evaluators with remainder bounds, recurrences/signs/special derivative values, differentiated reflection/multiplication, rational-argument values, and the finite polynomial recursion for Gamma derivatives. Derivative orders may remain external where the source explicitly allows that schema. The original first derivative at one is identified with the negative Euler–Mascheroni name. [GaussianGammaDigammaNative](Lean/IPRADerivations/Analysis/Gamma/Digamma/GaussianGammaDigammaNative.lean) constructs the original positive rational digamma as $Γ'/Γ$, verifies the product with the original Gamma name, and proves $ψ(1)=-γ$. [GaussianGammaDigammaStep](Lean/IPRADerivations/Analysis/Gamma/Digamma/Derivative/GaussianGammaDigammaStep.lean) binds the original derivative rate to literal rational increments $1/D$. [GaussianGammaDigammaDerivativeShift](Lean/IPRADerivations/Analysis/Gamma/Digamma/Derivative/GaussianGammaDigammaDerivativeShift.lean) derives the differentiated Gamma recurrence and [GaussianGammaDigammaRecurrence](Lean/IPRADerivations/Analysis/Gamma/Digamma/Derivative/GaussianGammaDigammaRecurrence.lean) proves $ψ(x+1)=ψ(x)+1/x$ at every encoded positive rational point. [GaussianGammaDigammaInteger](Lean/IPRADerivations/Analysis/Gamma/Digamma/ElementaryBounds/GaussianGammaDigammaInteger.lean) proves $ψ(n+1)=H_n-γ$ with an explicit independent-observation bound. [GaussianGammaDigammaFiniteSum](Lean/IPRADerivations/Analysis/Gamma/Digamma/Series/GaussianGammaDigammaFiniteSum.lean) proves the finite reciprocal-sum formula for every internal natural shift of the original positive rational digamma. [GaussianGammaDigammaGammaComparison](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaGammaComparison.lean) proves the symmetric product inequality for original Gamma at a positive rational increment. [GaussianGammaDigammaMonotone](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaMonotone.lean) passes the verified derivative rates through the comparison and cancels positive Gamma factors to prove monotonicity of the original digamma. [GaussianGammaDigammaSeries](Lean/IPRADerivations/Analysis/Gamma/Digamma/GaussianGammaDigammaSeries.lean) proves the cofinal C28 rate for all encoded positive rational inputs, and [GaussianGammaDigammaSeriesTerms](Lean/IPRADerivations/Analysis/Gamma/Digamma/Series/GaussianGammaDigammaSeriesTerms.lean) binds the finite correction to the literal reciprocal differences of the paper. [GaussianGammaDigammaPositiveTerms](Lean/IPRADerivations/Analysis/Gamma/Digamma/Series/GaussianGammaDigammaPositiveTerms.lean) proves the original positive-term C27 representation, and [GaussianGammaDigammaEulerDerivative](Lean/IPRADerivations/Analysis/Gamma/Digamma/Derivative/GaussianGammaDigammaEulerDerivative.lean) bounds the literal finite Euler slope against the original digamma with independent observation clocks. [GaussianGammaDigammaElementaryBounds](Lean/IPRADerivations/Analysis/Gamma/Digamma/ElementaryBounds/GaussianGammaDigammaElementaryBounds.lean) and [GaussianGammaDigammaElementaryOriginalLog](Lean/IPRADerivations/Analysis/Gamma/Digamma/ElementaryBounds/GaussianGammaDigammaElementaryOriginalLog.lean) prove the elementary logarithmic bracket on the original positive rational digamma with either original logarithm presentation. The polygamma and differentiated identity claims remain open. |
| 37–42 | [GaussianGammaCanonicalCoefficientRecurrence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/CanonicalProducts/GaussianGammaCanonicalCoefficientRecurrence.lean) proves the C42 equality of the actual regular canonical coefficient and finite sum names. [GaussianGammaCanonicalRecurrenceZetaFormula](Lean/IPRADerivations/Analysis/Gamma/Zeta/Coefficients/GaussianGammaCanonicalRecurrenceZetaFormula.lean) identifies the right name with the original gamma and signed zeta formula at the same observations. The remaining local Taylor/log-Gamma expansions, Laurent constants and remainders at each pole, positive-integer-centered expansions, vertical modulus products, and balanced parameter products still require their named coefficient and discarded-tail comparisons. |
| 43–48 | Quantitative strict convexity, effective Bohr–Mollerup uniqueness at fixed presentations, Wendel/Gautschi inequalities, rate-bearing Gamma ratios, actual positive-minimum location and negative-pole interval extremum/sign constructions. [GaussianGammaEulerRationalHeadConvexity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Convexity/GaussianGammaEulerRationalHeadConvexity.lean) proves the weighted powered comparison on the original positive rational finite Euler heads. [GaussianGammaEulerRationalLogConvexity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Convexity/GaussianGammaEulerRationalLogConvexity.lean) proves exact weighted convexity on the original finite Euler logarithms. [GaussianNamedPositiveLogarithmRate](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianNamedPositiveLogarithmRate.lean) proves quantitative transport through the named logarithm at a common positive lower bound. [GaussianGammaEulerRationalLogConvergence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/RationalLogarithm/GaussianGammaEulerRationalLogConvergence.lean) proves the quantitative log convergence using the explicit cofinal positive margin. [GaussianGammaNativeLogConvexity](Lean/IPRADerivations/Analysis/Gamma/Convexity/GaussianGammaNativeLogConvexity.lean) passes the exact weighted convexity inequality to the native log-Gamma names on all encoded positive rational arguments. [GaussianGammaNativeMidpointLogGap](Lean/IPRADerivations/Analysis/Gamma/Convexity/GaussianGammaNativeMidpointLogGap.lean) adds the explicit margin $(a-d)^2/(a+d)^2$ to twice the native log-Gamma at the midpoint for positive rational endpoints $a/b$ and $d/b$. [GaussianGammaNativeWeightedLogGap](Lean/IPRADerivations/Analysis/Gamma/Convexity/GaussianGammaNativeWeightedLogGap.lean) extends this explicit margin to the sums with arbitrary positive natural weights. [GaussianGammaNativeStrictLogConvexity](Lean/IPRADerivations/Analysis/Gamma/Convexity/GaussianGammaNativeStrictLogConvexity.lean) proves strict log-convexity on distinct encoded positive rationals by negating reverse order. [GaussianGammaNativeStrongLogConvexity](Lean/IPRADerivations/Analysis/Gamma/Convexity/GaussianGammaNativeStrongLogConvexity.lean) proves the full weight-dependent modulus from the paper, with additive margin $rs(d-a)^2/(2(r+s)B^2)$ in the unnormalized comparison at $a/b,d/b$ with upper endpoint bound $B/b$ and natural weights $r>0,s\ge0$. [GaussianGammaRationalGautschi](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalGautschi.lean) proves both strict Gautschi bounds $x^{1-u}<\Gamma(x+1)/\Gamma(x+u)<(x+1)^{1-u}$ for all encoded positive rational $x$ and rational $0<u<1$. It verifies that multiplying the original quotient by the original denominator recovers the numerator. [GaussianGammaRationalWendelGautschi](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalWendelGautschi.lean) proves both strict Wendel bounds on the normalized Gamma quotient and [GaussianGammaRationalWendelBinding](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalWendelBinding.lean) verifies the defining product with its original denominator. [GaussianGammaRationalWendelBoundary](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalWendelBoundary.lean) establishes both exact boundary values and the full weak Wendel interval. [GaussianGammaRationalWendelUniformLog](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalWendelUniformLog.lean) proves the uniform signed logarithmic rate for the original normalized Wendel ratio, including the one-quarter bound on its error coefficient. [GaussianGammaRationalWendelUniform](Lean/IPRADerivations/Analysis/Gamma/Ratios/GaussianGammaRationalWendelUniform.lean) proves the uniform relative error $0\le1-Q\le u(1-u)/x\le1/(4x)$ on the original named Wendel quotient for all rational weights in the unit interval. [GaussianGammaDigammaTwoShiftBinding](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/GaussianGammaDigammaTwoShiftBinding.lean) identifies the original normalized two-shift Gamma quotient by its exact product with its denominator. [GaussianGammaDigammaTwoShiftRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/GaussianGammaDigammaTwoShiftRate.lean) and [GaussianGammaDigammaTwoShiftRelativeRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftRelativeRate.lean) prove the C46 logarithmic and relative rates for common-denominator positive rational base and endpoints, with signed rational shifts and the source inequalities on the positive integer shift bound and base. The logarithmic bound is on the certified exponent of the quotient. [The exact rational-window rates](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftRationalRate.lean) give the original constants for every rational shift window, including noninteger bounds. Extension to regular named inputs remains open. [GaussianGammaDigammaLipschitz](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaLipschitz.lean) proves the original digamma upper slope $2(y-x)$ for common-denominator rational $1\le x\le y$ at independent observation clocks. [GaussianGammaDigammaRescaling](Lean/IPRADerivations/Analysis/Gamma/Digamma/Series/GaussianGammaDigammaRescaling.lean) verifies that positive rescaling preserves the native digamma value. [GaussianGammaDigammaDyadicCrossing](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaDyadicCrossing.lean) gives the bounded scan for adjacent opposite sample signs under the two endpoint tests. [GaussianGammaDigammaSlopeLowerRational](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaSlopeLowerRational.lean) proves the lower slope $(y-x)/4$ on $[1,2]$ with separate rational encodings. [GaussianGammaDigammaDyadicMesh](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaDyadicMesh.lean) bounds the increase on adjacent dyadic samples by $4\cdot 2^{-(p+6)}$, and [GaussianGammaDigammaGridSign](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaGridSign.lean) passes this bound to the absolute residual when the samples have opposite signs. [GaussianGammaDigammaCriticalSigns](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaCriticalSigns.lean) proves $\psi(1)<-1/4$ and $\psi(2)>1/4$ for the original names. [GaussianGammaDigammaDyadicEndpoints](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaDyadicEndpoints.lean) verifies their finite grid samples at every prescribed clock, and [GaussianGammaDigammaDyadicLocation](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaDyadicLocation.lean) constructs a regular primitive recursive location by comparing selected opposite-sign cells at independent clocks. The checked bound on the sampled digamma residual is $4\cdot 2^{-(p+6)}$. [GaussianGammaDigammaLocationInput](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationInput.lean) identifies the actual frozen inputs of the named integrals with the selected fractions. [GaussianGammaDigammaLocationResidual](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationResidual.lean) lifts the scalar digamma residual to an independent-clock Gaussian distance. [GaussianGammaDigammaLocationProduct](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationProduct.lean) uses a uniform bound on the original Gamma name to give a vanishing residual for the first logarithmic integral. [GaussianGammaDigammaPositiveStationary](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaPositiveStationary.lean) proves equality of the original first named logarithmic integral to zero at the completed location and transfers the original first derivative error bound to difference quotients at that point. [GaussianGammaDigammaLocationInterior](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationInterior.lean) places the completed location in $[17/16,31/16]$. [GaussianGammaDigammaLocationValue](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationValue.lean) proves that the actual named quotient $\Gamma^{\prime}/\Gamma$ is zero at this regular interior point. [GaussianGammaPositiveRationalProperness](Lean/IPRADerivations/Analysis/Gamma/Names/Input/GaussianGammaPositiveRationalProperness.lean) transports original Gamma between encodings with different denominators, radii and lower certificates. [GaussianGammaMinimumSignedStep](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumSignedStep.lean) identifies the literal signed small-step endpoint with the weighted chord center and verifies the original derivative rate there. [GaussianGammaMinimumQuotientReadback](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumQuotientReadback.lean) recovers the original endpoint variation with the exact step factor. [GaussianGammaMinimumChord](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumChord.lean) proves the asymmetric strong chord in both endpoint orders with a squared rational margin uniform in the weight. [GaussianGammaMinimumCenterRate](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumCenterRate.lean) transfers the derivative residual to the original log-Gamma endpoint variation along the thin chord. [GaussianGammaMinimumChordStationary](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumChordStationary.lean) cancels the weight with the thin-step rate and eliminates the intermediate observation allowances while preserving the strong margin. [GaussianGammaMinimumFreezeRational](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumFreezeRational.lean) and [GaussianGammaMinimumFreezeLocation](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumFreezeLocation.lean) read the actual named log-Gamma and native positive rational freezes with the independent-clock rate. [GaussianGammaMinimumFreezeOrder](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumFreezeOrder.lean) transfers their weak and strict logarithm orders to the original Gamma names. [GaussianGammaNegativeCriticalCorrection](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalCorrection.lean) computes the literal reciprocal correction for every negative interval. [GaussianGammaNegativeCriticalSigns](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalSigns.lean) proves margins of $-5$ and $5$ at the two prescribed endpoints and the corresponding opposite finite signs for the shifted digamma name. [GaussianGammaNegativeCriticalLowerSlope](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalLowerSlope.lean) proves a quarter lower slope throughout the interval, and [GaussianGammaNegativeCriticalSlope](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalSlope.lean) gives the explicit upper slope $2+(N+2)K^2$ on windows where both distances from the poles are at least $1/K$. [GaussianGammaNegativeCriticalGrid](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalGrid.lean) selects adjacent opposite signs at every dyadic mesh with a vanishing sampled residual. [GaussianGammaNegativeCriticalLocation](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/GaussianGammaNegativeCriticalLocation.lean) proves regularity of the original dyadic location, and [GaussianGammaNegativeCriticalLocationInterior](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalLocationInterior.lean) puts it strictly between $-N-1$ and $-N$. [GaussianGammaNegativeCriticalLocationZero](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/NegativeIntervals/GaussianGammaNegativeCriticalLocationZero.lean) constructs the zero value of the shifted digamma at that location by explicit cofinal evaluation. [GaussianGammaNegativeIntervalNative](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/GaussianGammaNegativeIntervalNative.lean) proves that the original Gamma name times the literal repeated shift product gives the positive terminal Gamma name at $1+a/b$. [GaussianGammaNegativeIntervalDerivativeTarget](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalDerivativeTarget.lean) verifies the algebraic identities for the proposed derivative target. [GaussianGammaNegativeProductDerivativeCorrection](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/Products/GaussianGammaNegativeProductDerivativeCorrection.lean) identifies the first coefficient of the literal product with the negative of the digamma correction times that product. [GaussianGammaNegativeProductDerivativeRate](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/Products/GaussianGammaNegativeProductDerivativeRate.lean) proves its finite derivative error proportional to the displacement. [GaussianGammaNegativeIntervalProductSign](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalProductSign.lean) bounds the signed product below by $a(b-a)/b^2$ throughout the open interval. [GaussianGammaNegativeIntervalGammaSign](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalGammaSign.lean) gives an explicit positive lower bound on the sign-adjusted original Gamma over encoded rational inputs. [GaussianGammaNegativeIntervalInverseRecurrence](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Recurrence/GaussianGammaNegativeIntervalInverseRecurrence.lean) proves the inverse recurrence and identifies its two-term derivative target. [GaussianGammaNegativeIntervalInverseBound](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalInverseBound.lean) and [GaussianGammaNegativeIntervalStep](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalStep.lean) certify bounds and the original positive Euler rate at a native unit step. [GaussianGammaNegativeIntervalDigammaRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalDigammaRate.lean) proves that the original negative Gamma difference quotient at any rational input converges along steps $1/D$ to the Gamma value times the literal shifted digamma, and that its normalization by the original Gamma converges to the shifted digamma itself. It supplies an explicit cutoff and separate allowances for both observation clocks. [GaussianGammaNegativeIntervalCriticalQuotientZero](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalCriticalQuotientZero.lean) and [GaussianGammaNegativeIntervalCriticalDerivativeZero](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalCriticalDerivativeZero.lean) prove that actual normalized and unnormalized Gamma quotients at the selected dyadic inputs give regular zero names, with explicit cofinal unit steps. [GaussianGammaNegativeIntervalLogAbsolute](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalLogAbsolute.lean) verifies that the named exponential of the real logarithm is the original Gamma after correcting its interval sign, and [GaussianGammaNegativeIntervalLogAbsoluteOrder](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalLogAbsoluteOrder.lean) transfers both weak and strict orders to that magnitude. [GaussianGammaNegativeIntervalLogStrongConvexity](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalLogStrongConvexity.lean) gives its strong weighted logarithmic comparison with an explicit quadratic margin on every negative rational interval. [GaussianGammaNegativeIntervalChordRate](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalChordRate.lean) gives the original signed thin-chord Gamma derivative rate in either endpoint order. [GaussianGammaNegativeIntervalLogThinChord](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalLogThinChord.lean) retains $|c-a|^2/(16b^2)$ in the unnormalized chord and [GaussianGammaNegativeIntervalLogChordStationary](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalLogChordStationary.lean) makes the stationary comparison conditional on the corresponding thin-step logarithmic rate. [GaussianGammaNegativeIntervalUniformLower](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalUniformLower.lean) gives the signed Gamma magnitude a floor independent of its rational encoding, and [GaussianGammaNegativeIntervalLogAbsoluteRetiming](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalLogAbsoluteRetiming.lean) binds the resulting retimed positive logarithm to the original log magnitude. [GaussianGammaNegativeIntervalCriticalComparison](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalCriticalComparison.lean) then proves the strong comparison at the actual selected critical approximants against distinct rational inputs with the same denominator and a common pole margin. Its leading error tends to zero with an interval-dependent coefficient, and the two observation allowances remain independent. [GaussianGammaNegativeIntervalCriticalRationalComparison](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalCriticalRationalComparison.lean) removes the common-denominator and apartness premises while preserving the exact squared gap and the same error. [GaussianGammaNegativeIntervalNamedInput](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Input/GaussianGammaNegativeIntervalNamedInput.lean) verifies the selected offset's named pole margin, and [GaussianGammaNegativeIntervalNamedInputRetiming](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Input/GaussianGammaNegativeIntervalNamedInputRetiming.lean) obtains an exact sample collar by reading a sufficiently late observation of any regular real offset with named order margins. [GaussianGammaNegativeIntervalRationalProperness](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Input/GaussianGammaNegativeIntervalRationalProperness.lean) identifies the decoded critical fraction with the literal grid fraction and proves equal-encoding coherence of the original signed Gamma and log magnitude. [GaussianGammaNegativeIntervalNamedApartness](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedApartness.lean) keeps the squared comparison gap positive at every sufficiently late observation when the offsets are apart. [GaussianGammaNegativeIntervalNamedComparisonTransfer](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedComparisonTransfer.lean) transfers finite comparisons with a persistent margin to the regular names. [GaussianGammaNegativeIntervalNamedDigammaRationalRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigammaRationalRate.lean) and [GaussianGammaNegativeIntervalNamedDigamma](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigamma.lean) construct the regular named shifted digamma and bound its distance from the actual rational digamma at every frozen observation. [GaussianGammaNegativeIntervalNamedDigammaInverseSlope](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigammaInverseSlope.lean) carries the lower slope to the named offsets. [GaussianGammaNegativeIntervalNamedDigammaUniqueness](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigammaUniqueness.lean) proves injectivity under separate pole margins. [GaussianGammaNegativeIntervalNamedDigammaRoot](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigammaRoot.lean) identifies the literal critical grid offset as the unique zero, including inputs admitted through named interval order and retiming. [GaussianGammaNegativeIntervalNamedLogTerminal](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalNamedLogTerminal.lean) supplies a modulus for the original positive terminal Gamma across distinct rational encodings, and [GaussianGammaNegativeIntervalNamedLogVariation](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalNamedLogVariation.lean) extends it through the negative shift and logarithm. [GaussianGammaNegativeIntervalNamedLog](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalNamedLog.lean) constructs regular real log-magnitude names by sampling the original evaluations. [GaussianGammaNegativeIntervalNamedLogFrozen](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Logarithms/GaussianGammaNegativeIntervalNamedLogFrozen.lean) proves the uniform late-freeze bound with independent output clocks. [GaussianGammaNegativeIntervalNamedMinimum](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedMinimum.lean) and [GaussianGammaNegativeIntervalNamedStrictMinimum](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedStrictMinimum.lean) establish the weak log-magnitude minimum and its strict form with positive separation. [GaussianGammaNegativeIntervalNamedGamma](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedGamma.lean) identifies Gamma on the named interval by a uniform rate to the literal unscaled rational Gamma evaluator. [GaussianGammaNegativeIntervalNamedExtremum](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedExtremum.lean) proves the parity-dependent Gamma extrema under named interval bounds and preserves strictness when the original offset is apart. [GaussianGammaNegativeIntervalNamedGammaSign](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedGammaSign.lean) certifies real observations and the strict interval sign. [GaussianGammaNegativeIntervalNamedDigammaQuotient](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedDigammaQuotient.lean) and [GaussianGammaNegativeIntervalNamedSignedDigammaQuotient](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalNamedSignedDigammaQuotient.lean) identify the normalized original forward unit quotients with the named digamma along the explicit cofinal rational freezes. [GaussianGammaNegativeIntervalSignedDigammaQuotient](Lean/IPRADerivations/Analysis/Gamma/Digamma/NegativeAxis/GaussianGammaNegativeIntervalSignedDigammaQuotient.lean) proves exact cancellation of the signed factors. [GaussianGammaNegativeIntervalNamedDerivative](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalNamedDerivative.lean) gives a uniform rational offset clock and an explicit step cutoff for the original unscaled forward quotients, with limit the product of named Gamma and named digamma. [GaussianNamedApartnessTightness](Lean/IPRADerivations/Analysis/Names/Apartness/GaussianNamedApartnessTightness.lean) and [GaussianGammaNegativeIntervalNamedExtremumUniqueness](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedExtremumUniqueness.lean) prove that an offset attaining the extremal value equals the selected offset, using finite rational comparisons inside iPRA. [GaussianGammaMinimumRational](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/GaussianGammaMinimumRational.lean) preserves the squared rational separation term with an explicit stationary residual allowance. [GaussianGammaMinimumGlobal](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/GaussianGammaMinimumGlobal.lean) proves that the selected positive location is a global minimum of the original named Gamma on all positive real inputs with a lower certificate, with strict inequality for every input finitely apart from the minimizer. [GaussianGammaNamedPoleFreeModulus](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeModulus.lean), [GaussianGammaNamedPoleFree](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFree.lean), [GaussianGammaNamedPoleFreeEncoding](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeEncoding.lean), and [GaussianGammaNamedPoleFreeFrozen](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeFrozen.lean) construct the regular pole-free complex Gamma evaluator from the original native observations with a uniform disk and pole separation. [GaussianGammaNegativeIntervalNamedGammaNativeDomain](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Input/GaussianGammaNegativeIntervalNamedGammaNativeDomain.lean) certifies the affine negative-interval input, and [GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding.lean) proves equality of the two Gamma names at that input. [GaussianGammaNegativeIntervalNamedTerminalDerivative](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalNamedTerminalDerivative.lean) proves the rate for the original positive terminal quotient and preserves the named increment. [GaussianGammaNegativeIntervalInverseRationalEnvelope](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalInverseRationalEnvelope.lean) gives the exact rational inverse-shift difference and quadratic remainder. [GaussianGammaNegativeIntervalNamedInverseFactor](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedInverseFactor.lean) and [GaussianGammaNegativeIntervalNamedCorrectionFactor](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedCorrectionFactor.lean) extend the exact inverse shift and its derivative coefficient to named inputs. [GaussianGammaNegativeIntervalNamedInverseDerivative](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalNamedInverseDerivative.lean) proves the named-increment rate for the original inverse factor. [GaussianNamedIncrementProductRule](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedIncrementProductRule.lean) proves the exact named-increment product rule, and [GaussianGammaNegativeIntervalNamedInverseRecurrence](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Recurrence/GaussianGammaNegativeIntervalNamedInverseRecurrence.lean) and [GaussianGammaNegativeIntervalNamedDerivativeRecurrence](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Recurrence/GaussianGammaNegativeIntervalNamedDerivativeRecurrence.lean) identify the original recurrence and derivative target using common terminal freezes. [GaussianGammaNamedPoleFreeProperness](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeProperness.lean) proves extensionality of the native pole-free evaluator under independent certificates, and [GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient.lean) preserves the original named reciprocal through the affine shift. [GaussianGammaNegativeIntervalNamedIncrementDerivative](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalNamedIncrementDerivative.lean) verifies that the original quotient converges to named Gamma times shifted digamma for every regular named real increment satisfying the explicit smallness and separation certificates. [GaussianGammaNegativeIntervalNamedGammaInverse](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Values/GaussianGammaNegativeIntervalNamedGammaInverse.lean) and [GaussianGammaNegativeIntervalNamedStationary](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedStationary.lean) cancel the nonzero named Gamma factor. [GaussianGammaNegativeIntervalNamedDerivativeMargin](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/Derivatives/GaussianGammaNegativeIntervalNamedDerivativeMargin.lean) proves derivative extensionality across independently certified pole margins. [GaussianGammaNegativeIntervalNamedCritical](Lean/IPRADerivations/Analysis/Gamma/NegativeAxis/CriticalPoints/GaussianGammaNegativeIntervalNamedCritical.lean) gives the actual quotient rate to zero at the selected point and both directions of the critical-point classification for offsets supplied with named interval bounds. [GaussianBohrMollerupUniqueness](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/GaussianBohrMollerupUniqueness.lean) proves effective uniqueness for fixed logarithmic presentations satisfying the internal laws, with a two-chord comparison and cutoff $j=1+a(a+b)2^p$ at $a/b$. [GaussianBohrMollerupPositivePresentation](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/Named/GaussianBohrMollerupPositivePresentation.lean) identifies positive presentations with the actual Gamma name. [The literal bracket enclosure](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketEnclosure.lean) proves both original general-block bracket inequalities. [The literal width](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketWidth.lean) gives the paper’s rational bound and dyadic cutoff. [The literal squeeze](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/GaussianBohrMollerupLiteralUniqueness.lean) uses exactly that cutoff for uniqueness. [The named extension](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/Named/GaussianBohrMollerupNamedGamma.lean) evaluates each fixed verified rational presentation on actual late positive real input observations and identifies its lifted logarithm and exponential with the original named values. This gives the fixed-presentation uniqueness claim via these chords. The paper’s specific finite $L_n/U_n$ approximation intervals are separate. |
| 49–53 | Leading Stirling/relative errors, Robbins bounds, every fixed order of log-Stirling and digamma expansions with the signed positive-real-axis remainder, and the actual multiplicative-coefficient/error algorithm. Generic Euler–Maclaurin components need application-specific endpoint and positivity proofs. [GaussianStirlingNames](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingNames.lean) constructs the regular real name of $A(x)$ on every encoded positive rational, using the original Gamma and harmonic logarithms. [GaussianStirlingConstant](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingConstant.lean) constructs the regular real name of $C=\tfrac12\log(2\pi)$. [GaussianStirlingRecurrence](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingRecurrence.lean) gives the original named equality $A(x)-A(x+1)=d(x)$. [StirlingRationalSeries](Lean/IPRADerivations/Analysis/Stirling/StirlingRationalSeries.lean), [GaussianStirlingRationalTelescopers](Lean/IPRADerivations/Analysis/Stirling/Telescoping/GaussianStirlingRationalTelescopers.lean), and [GaussianStirlingFiniteSeries](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingFiniteSeries.lean) prove the rational finite series estimate, its exact Horner representation, and the matching telescopers with positive margins. [GaussianStirlingDifferenceBrackets](Lean/IPRADerivations/Analysis/Stirling/Telescoping/GaussianStirlingDifferenceBrackets.lean) proves the original finite odd-series logarithm brackets on the full positive rational domain. [GaussianStirlingDifferenceBounds](Lean/IPRADerivations/Analysis/Stirling/Telescoping/GaussianStirlingDifferenceBounds.lean) proves the sharp local inequalities and exact rational finite endpoint order. [GaussianStirlingOriginalIntegerLimit](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingOriginalIntegerLimit.lean) constructs the regular integer limit name with exact tail $1/(12n)$ and independent observation errors. [GaussianStirlingLogDuplication](Lean/IPRADerivations/Analysis/Stirling/Duplication/GaussianStirlingLogDuplication.lean) proves original log-Gamma duplication on the Stirling inputs. [GaussianStirlingDuplication](Lean/IPRADerivations/Analysis/Stirling/Duplication/GaussianStirlingDuplication.lean) proves the exact positive rational Stirling duplication identity with the original $C$ and the signed residual $1/2-x\log(1+1/(2x))$. [GaussianStirlingWallisGammaRatio](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianStirlingWallisGammaRatio.lean) identifies the actual half-integer and integer Gamma ratio with the finite Wallis factor. [GaussianStirlingWallisLogRate](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianStirlingWallisLogRate.lean) gives its logarithmic rate $12/n+29\cdot 2^{-p}$ for $n\ge 6$ at clock $p$. [GaussianStirlingWallisLogIdentity](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianStirlingWallisLogIdentity.lean) relates this logarithm exactly to the original Gamma logarithms. [GaussianStirlingDuplicationResidual](Lean/IPRADerivations/Analysis/Stirling/Duplication/GaussianStirlingDuplicationResidual.lean) proves the residual bound $1/(4x)+3\cdot 2^{-p}$ on the original name. [GaussianStirlingHalfStep](Lean/IPRADerivations/Analysis/Stirling/Duplication/GaussianStirlingHalfStep.lean) derives a distance $64(1/n+2^{-p})$ between original samples at $n+1/2$ and $n$ for $n\ge 6$. [GaussianStirlingConstantIdentification](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingConstantIdentification.lean) proves unconditional equality of the actual cofinal integer limit and $C=\tfrac12\log(2\pi)$ in object iPRA. [GaussianStirlingGlobalBounds](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingGlobalBounds.lean) retains both sharp finite margins and proves the first-order log remainder bounds under a translated cofinal rate. It derives the rate at integer inputs. [GaussianStirlingRobbins](Lean/IPRADerivations/Analysis/Stirling/Robbins/GaussianStirlingRobbins.lean) proves both sharp logarithmic Robbins inequalities, including the explicit lower and upper margins, unconditionally at positive integers. [GaussianStirlingMultiplicative](Lean/IPRADerivations/Analysis/Stirling/GaussianStirlingMultiplicative.lean) identifies the exponential of the original log remainder with the literal positive rational Stirling quotient and verifies the positive square root and denominator inverse. [GaussianStirlingGlobalBoundsShiftCorrection](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingGlobalBoundsShiftCorrection.lean) bounds the elementary part of the cofinal positive-rational shift by $5/n+3\cdot2^{-p}$. [GaussianStirlingGlobalBoundsRemainder](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingGlobalBoundsRemainder.lean) proves the exact named finite remainder decomposition. [GaussianStirlingGlobalBoundsTranslatedRate](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingGlobalBoundsTranslatedRate.lean) reduces the cofinal rational rate and sharp global bounds to the original fractional log-Gamma increment estimate. [GaussianStirlingMultiplicativeBoundsCaps](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingMultiplicativeBoundsCaps.lean) derives the relative error bound $1/(6x)$ for $x\ge1$ from the sharp first-order logarithmic remainder. [GaussianStirlingFactorialRobbins](Lean/IPRADerivations/Analysis/Stirling/Robbins/GaussianStirlingFactorialRobbins.lean) proves $1<R_n<12n/(12n-1)$ for the literal factorial ratio and $R_n<1+2^{-p}$ for $n\ge2^p$. [GaussianStirlingGammaFractionalIncrement](Lean/IPRADerivations/Analysis/Stirling/GammaIncrements/GaussianStirlingGammaFractionalIncrement.lean) proves the actual fractional log-Gamma estimate and discharges the cofinal hypotheses. It proves the sharp first-order log remainder and the positive finite-series tail for all encoded positive rationals, and both sharp logarithmic Robbins bounds for encoded rationals at least one. [GaussianStirlingFactorialRobbinsExponential](Lean/IPRADerivations/Analysis/Stirling/Robbins/GaussianStirlingFactorialRobbinsExponential.lean) proves the classical strict exponential caps for the literal factorial quotient. [GaussianStirlingGlobalMultiplicativeBounds](Lean/IPRADerivations/Analysis/Stirling/Bounds/GaussianStirlingGlobalMultiplicativeBounds.lean) proves the strict leading exponential comparison for all encoded positive rationals, the strict relative-error bound for $x\ge1$, and the strict exponential Robbins bounds on $x\ge1$. [GaussianStirlingFactorialRobbinsConventionalRatio](Lean/IPRADerivations/Analysis/Stirling/Robbins/GaussianStirlingFactorialRobbinsConventionalRatio.lean) binds that same factorial quotient to the literal conventional formula $R_n n^n\sqrt{2\pi n}=n!e^n$. [GaussianStirlingAllOrderPairedRefinement](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedRefinement.lean) proves a positive reflected inverse-power weight gap uniform under mesh refinement. [GaussianStirlingAllOrderCenteredBernoulli](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderCenteredBernoulli.lean) binds the centered kernel to the original Bernoulli mesh with exact reflection and zero endpoints. [GaussianStirlingExpansionCoefficients](Lean/IPRADerivations/Analysis/Stirling/Expansions/GaussianStirlingExpansionCoefficients.lean) proves the fixed-order coefficient recurrence and initial coefficient. [GaussianStirlingExpansionErrorProgram](Lean/IPRADerivations/Analysis/Stirling/Expansions/GaussianStirlingExpansionErrorProgram.lean) proves an explicit multiplicative approximation and error algorithm for the original quotient from the corresponding higher logarithmic rate. [GaussianStirlingAllOrderBernoulliShape](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliShape.lean) proves that the actual centered Bernoulli polynomial has a nonnegative coefficient expansion in $4t(1-t)$ with a positive coefficient. [GaussianStirlingAllOrderBernoulliMeshOrder](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliMeshOrder.lean) proves monotonicity on the first half of the literal grid. [GaussianStirlingAllOrderBernoulliMeshRefinement](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliMeshRefinement.lean) proves exact refinement invariance. [GaussianStirlingAllOrderBernoulliMeshMargin](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliMeshMargin.lean) gives the explicit positive gap on the separated subintervals at all refinements. [GaussianStirlingExpansionFirstOrder](Lean/IPRADerivations/Analysis/Stirling/Expansions/GaussianStirlingExpansionFirstOrder.lean) identifies the literal first-order output with $1+1/(12x)$ and discharges its analytic premise from the proved rational Robbins bracket. [GaussianStirlingAllOrderBernoulliEnvelope](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliEnvelope.lean) bounds the original centered kernel by its exact midpoint value on the full rational mesh. [GaussianStirlingAllOrderPanelTail](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderPanelTail.lean) proves the uniform reciprocal-power tail for its actual finite weighted panels. [GaussianStirlingAllOrderFirstPanel](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanel.lean) gives the exact partial fraction decomposition of the original first kernel on a panel. [GaussianStirlingCubicRate](Lean/IPRADerivations/Analysis/Stirling/Expansions/GaussianStirlingCubicRate.lean) proves the strict signed bracket $1/(12x)-1/(360x^3)<R(x)<1/(12x)$ at every encoded positive rational input, with a cubic rate at independent observations. [GaussianStirlingExpansionSecondOrder](Lean/IPRADerivations/Analysis/Stirling/Expansions/GaussianStirlingExpansionSecondOrder.lean) uses that rate to discharge the original multiplicative program through degree two. [GaussianStirlingAllOrderFirstPanelSum](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanelSum.lean) evaluates the original first weighted panel as the literal harmonic interval and reciprocal-square sum. [GaussianStirlingAllOrderFirstPanelSquareError](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanelSquareError.lean) relates the square contribution to one with an explicit finite-mesh rate. [GaussianStirlingAllOrderFirstPanelError](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanelError.lean) gives an explicit two-sided comparison between the literal first panel and twice the original harmonic-log difference. [GaussianStirlingAllOrderBoxProductGap](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Covariance/GaussianStirlingAllOrderBoxProductGap.lean) proves a positive crossed-product gap on separated refinable boxes for the original centered and reflected weight samples. [GaussianStirlingAllOrderFirstPanelImproper](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanelImproper.lean) identifies the original log-Stirling remainder with the actual first centered periodic Bernoulli weighted improper sum and proves its explicit cutoff error $46· 2^{-p}$. [GaussianStirlingAllOrderPanelDerivative](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderPanelDerivative.lean) gives the exact centered derivative complement and endpoint identities. [GaussianStirlingAllOrderDiscreteParts](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderDiscreteParts.lean) verifies exact finite summation by parts, and [GaussianStirlingAllOrderCentralDerivativeBinding](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Truncation/GaussianStirlingAllOrderCentralDerivativeBinding.lean) identifies the leading quadratic term of the centered finite difference with the actual lower Bernoulli grid, with a two-sided finite error. [GaussianStirlingAllOrderHalfGridMean](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderHalfGridMean.lean) proves the normalized reverse-Chebyshev inequality for the original reflected first-half grids, retaining a positive rational margin independent of refinement. [GaussianStirlingAllOrderPairedReadback](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedReadback.lean) identifies every weighted product with the two original periodic panel rows at its reflected indices. [RationalPowerMoments](Lean/IPRADerivations/Analysis/RationalArithmetic/Powers/RationalPowerMoments.lean) verifies the literal scalar monomial average and its $1/M$ mesh error against the exact monomial moment. [GaussianStirlingAllOrderCentralBernoulliError](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderCentralBernoulliError.lean) and [GaussianStirlingAllOrderReciprocalWeightError](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Truncation/GaussianStirlingAllOrderReciprocalWeightError.lean) verify the quantitative centered second-difference comparisons for the original Bernoulli and reciprocal-power panel factors. [GaussianStirlingAllOrderReciprocalGridError](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Truncation/GaussianStirlingAllOrderReciprocalGridError.lean) expresses the reciprocal curvature error uniformly on the literal panel grid. [GaussianStirlingAllOrderPairedPanel](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedPanel.lean) reads the original panel as exactly the paired half-grid with the literal midpoint correction. [RationalPolynomialGridSum](Lean/IPRADerivations/Analysis/Polynomials/GridSums/RationalPolynomialGridSum.lean) verifies a fixed signed polynomial grid fold through the natural power sums. [GaussianStirlingAllOrderPanelPartsRecurrence](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderPanelPartsRecurrence.lean) proves the quantitative integration-by-parts recurrence for the original finite panels with an explicit $1/M$ mesh error, and [GaussianStirlingAllOrderPowerIntegral](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PowerIntegrals/GaussianStirlingAllOrderPowerIntegral.lean) gives the adjacent antiderivative brackets for the reciprocal-power mass. The unweighted averages have exact reflected-grid identities with the appropriate midpoint and endpoint corrections in [GaussianStirlingAllOrderPairedWeightFold](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedWeightFold.lean) and [GaussianStirlingAllOrderPairedBernoulliFold](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedBernoulliFold.lean). [GaussianStirlingAllOrderBernoulliGridMean](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliGridMean.lean) identifies the literal centered Bernoulli samples with the signed polynomial whose constant coefficient has been removed. [RationalPolynomialGridMean](Lean/IPRADerivations/Analysis/Polynomials/GridSums/RationalPolynomialGridMean.lean) proves a two-sided mesh error for every fixed signed polynomial, and [GaussianStirlingAllOrderBernoulliGridRate](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderBernoulliGridRate.lean) specializes the exact moment and error to the original centered Bernoulli mean at each fixed positive order. [GaussianStirlingAllOrderPanelPartsCofinal](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderPanelPartsCofinal.lean) proves an explicit cofinal $2^{-p}$ residual for the exact original weighted and mass prefixes. [GaussianStirlingAllOrderFirstPanelCommonMesh](Lean/IPRADerivations/Analysis/Stirling/AllOrders/FirstPanel/GaussianStirlingAllOrderFirstPanelCommonMesh.lean) compares the actual first panel on arbitrary fine meshes with its original local logarithmic name. [GaussianStirlingAllOrderPowerIntegralMesh](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PowerIntegrals/GaussianStirlingAllOrderPowerIntegralMesh.lean) and [GaussianStirlingAllOrderPowerIntegralCofinal](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PowerIntegrals/GaussianStirlingAllOrderPowerIntegralCofinal.lean) identify the original reciprocal-power mass with its exact antiderivative, with a cofinal error uniform over the cutoff. [GaussianStirlingAllOrderPairedWeightMass](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderPairedWeightMass.lean) identifies this mass fold with the ordinary weight average used in the reflected comparison. [GaussianStirlingAllOrderPanelPartsBinding](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PanelParts/GaussianStirlingAllOrderPanelPartsBinding.lean) binds the literal cofinal weighted prefixes at every fixed order to the named recurrence based on the original remainder. [GaussianStirlingAllOrderImproperName](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderImproperName.lean) supplies the regular improper name and its equivalence to that recurrence. [GaussianDigammaFirstBernoulliPanelSum](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliPanelSum.lean) splits the first original digamma panel exactly into the literal reciprocal, square and cube mass folds. [GaussianDigammaFirstBernoulliEndpoints](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliEndpoints.lean) identifies the exact square and cube antiderivative correction with the reciprocal endpoint trapezoid. [GaussianStirlingAllOrderFullGridCovariance](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderFullGridCovariance.lean) transfers the positive reflected margin to the original full panel with an exact midpoint correction. [GaussianStirlingAllOrderFullGridMeanRate](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Bernoulli/GaussianStirlingAllOrderFullGridMeanRate.lean) inserts the signed Bernoulli mean with its mesh allowance, and [GaussianStirlingAllOrderMidpointCorrection](Lean/IPRADerivations/Analysis/Stirling/AllOrders/PairedPanels/GaussianStirlingAllOrderMidpointCorrection.lean) bounds the midpoint correction by the current reciprocal-power cap divided by $4S$. [GaussianStirlingAllOrderPanelPositive](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderPanelPositive.lean) and [GaussianStirlingAllOrderPanelPositivePrefix](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderPanelPositivePrefix.lean) prove a uniformly positive lower floor for the first original weighted panel and every nonempty prefix on meshes $8S$. [GaussianDigammaFirstBernoulliHarmonic](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliHarmonic.lean) proves the exact correction between the original left harmonic mass and the verified factorial-harmonic interval. [GaussianStirlingAllOrderLogTruncation](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Logarithms/GaussianStirlingAllOrderLogTruncation.lean) identifies the signed multiple of the actual improper name with the original log-Stirling remainder after subtracting each literal fixed truncation. [GaussianStirlingAllOrderTruncationCoefficients](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Truncation/GaussianStirlingAllOrderTruncationCoefficients.lean) checks the correction coefficients against the existing log coefficient formula. [GaussianStirlingAllOrderImproperPositive](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderImproperPositive.lean) passes the finite rational floor to the actual improper name and proves strict positivity. [GaussianStirlingAllOrderOuterCovariance](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Covariance/GaussianStirlingAllOrderOuterCovariance.lean) sums the corrected upper comparison over every nonempty original cutoff while retaining the first-panel margin. [GaussianStirlingAllOrderTruncationHorner](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Truncation/GaussianStirlingAllOrderTruncationHorner.lean) supplies the exact connection between the literal correction sums and the original Horner program at both parities. [GaussianStirlingAllOrderOuterCovarianceRate](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Covariance/GaussianStirlingAllOrderOuterCovarianceRate.lean) gives the uniform summed error and [GaussianStirlingAllOrderOuterCovarianceStrict](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Covariance/GaussianStirlingAllOrderOuterCovarianceStrict.lean) retains a fixed positive rational floor for the strict finite covariance gap. [GaussianStirlingAllOrderSignedLower](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderSignedLower.lean) transports strict positivity to the original oriented truncation error. [GaussianStirlingAllOrderNamedUpperGap](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Logarithms/GaussianStirlingAllOrderNamedUpperGap.lean) transfers the rational floor to the named difference. [GaussianStirlingAllOrderImproperUpper](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderImproperUpper.lean) proves the strict upper comparison on the actual improper name. [GaussianStirlingAllOrderSignedBounds](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderSignedBounds.lean) proves the sharp strict two-sided bound for the oriented original log-Stirling error at every fixed order and every encoded positive rational input. [GaussianDigammaFirstBernoulliLocal](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliLocal.lean) proves the explicit first-panel rate against the real log-difference name. [GaussianDigammaFirstBernoulliReference](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliReference.lean) gives the exact finite reference row as an anchor difference. [GaussianStirlingAllOrderSignedParity](Lean/IPRADerivations/Analysis/Stirling/AllOrders/ImproperBounds/GaussianStirlingAllOrderSignedParity.lean) gives the original un-oriented parity brackets. [GaussianStirlingAllOrderSharpLogRate](Lean/IPRADerivations/Analysis/Stirling/AllOrders/Logarithms/GaussianStirlingAllOrderSharpLogRate.lean) transfers those exact bounds to the original Horner errors, discharges the independent-clock log rate for positive rational inputs at least one, and proves the original multiplicative approximation program at every fixed degree under its explicit large-argument guard. [GaussianDigammaFirstBernoulliPrefix](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliPrefix.lean) and [GaussianDigammaFirstBernoulliImproper](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/FirstTerm/GaussianDigammaFirstBernoulliImproper.lean) sum the mesh errors and identify the native first cofinal weighted prefix with $\log x-1/(2x)-\psi(x)$, including the explicit required mesh and observation rate. [GaussianDigammaBernoulliRecurrence](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliRecurrence.lean) verifies the recurrence and its mesh rate at every fixed order. [GaussianDigammaBernoulliImproperName](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliImproperName.lean) gives explicit regular names for the literal weighted prefixes and their cross-clock equivalence to the recurrence. [GaussianDigammaBernoulliCoefficients](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliCoefficients.lean) verifies the coefficients against the original Bernoulli table. [GaussianDigammaBernoulliTruncation](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliTruncation.lean) identifies each actual improper name with $(-1)^{m+1}$ times the native error after subtracting the first $m$ inverse even powers on every encoded positive rational. [GaussianDigammaBernoulliActualBase](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliActualBase.lean) and [GaussianDigammaBernoulliActualUpper](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliActualUpper.lean) pass the positive lower floor and the sharp strict upper comparison to the actual improper names. [GaussianDigammaBernoulliRadius](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliRadius.lean) identifies that upper point with the magnitude of the first omitted term. [GaussianDigammaBernoulliSharpRemainder](Lean/IPRADerivations/Analysis/Gamma/Digamma/Bernoulli/GaussianDigammaBernoulliSharpRemainder.lean) proves the strict signed two-sided bound for the original digamma truncation after every fixed number $m$ of corrections on all encoded positive rationals. |
| 54–58 | [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerCofinal.lean) constructs the canonical Euler logarithm on the signed rational right half-plane from the original heads. Its exponential equals the original Gamma name by [GaussianLogGammaEulerExponentialLimit](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialLimit.lean). The unit shift, normalization at one and positive-rational-axis identity are checked below. The cofinal Taylor comparison with the reciprocal slope is checked below. The actual punctured difference quotient converges to the C27 digamma series on these rational charts. The canonical program also gives a regular log-Gamma evaluator on regular complex names with a certified right-half-plane margin. Its exponential agrees with the original named Gamma, including the overlap with the general pole-free evaluator. The actual named derivative is the cofinal digamma series, with a uniform modulus. The exact unit-shift recurrence holds for regular input names on the same certified right half-plane. On the certified positive real axis the same named evaluator equals the original real log-Gamma. The actual Binet kernel series has the uniform `1/(8N)` truncation bound and the interval estimates recorded below. Its value at zero is `1/12`, which is also the sharp upper bound on the nonnegative axis. [The elementary kernel proof](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelElementaryRational.lean) identifies its quotient at positive rational times and its value at zero. [The first Binet formula](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormula.lean) identifies the original improper Laplace sampler with the original Stirling remainder on the encoded rational right half-plane. [The named first Binet formula](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormulaNamed.lean) extends the identity to regular complex names with the original positive real-part margin and disk. [The second Binet improper integral](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseImproperName.lean) is a regular name for the original integrand with checked lower and upper cutoff rates. [The second Binet formula](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFormula.lean) identifies twice this original improper integral with the original Stirling remainder on the encoded rational right half-plane. [The named second Binet formula](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFormulaNamed.lean) lifts that original sampler to regular complex names with the certified margin and disk. [Raabe’s formula](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeFormula.lean) holds for the original unit-interval log-Gamma quadrature at every encoded positive rational input. [The cofinal frozen-grid formula](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeNamedGrid.lean) extends it to regular positive real names with a certified margin, using actual late input observations and every sufficiently fine mesh at each such base. [The original improper unit integral at zero](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeUnitIntegral.lean) equals the named Stirling constant. [The shifted unit integral](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeShiftedUnitFormula.lean) equals the same constant minus one. [The actual Binet forward quotient](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentForwardQuotient.lean) converges to the negative successor moment at each encoded positive rational base, with explicit observation and step errors. [The two-sided derivative](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentBackwardQuotient.lean) compares both original quotients to the same negative successor moment for every internal order at encoded positive rational inputs. [The named moment evaluator](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamed.lean) extends the original moments to regular inputs on the certified positive real axis. [Named strict positivity](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedPositive.lean) has the uniform explicit [1,2] panel floor at all internal orders. [Both original named quotients](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedDerivative.lean) converge to the negative successor moment at the same base with explicit error budgets uniform in the physical margin. Together with the zeroth identity and strict positivity, this gives complete monotonicity of the original named Stirling remainder. [The original Mellin improper integral](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinImproper.lean) and [Gamma times the original Dirichlet name](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletProduct.lean) are regular on the certified half-plane. [The original Gamma–zeta Mellin identity](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinIdentity.lean) proves their equality for encoded complex rational parameters with the certified real-part margin. [The factorized named formula](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedMellin.lean) extends the identity to regular complex parameters with a certified margin above one, using the original named Gamma of the actual input and the separately lifted original Dirichlet series. [The original specialization at two](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinBasel.lean) equates the actual improper sampler with the original pi-square name divided by six. |
| 59–62 | Wallis product with a rational rate to the original arctangent quadrature checked in [GaussianGammaHalfWallisRate](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianGammaHalfWallisRate.lean). [GaussianEvenMomentIntegral](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianEvenMomentIntegral.lean) checks the actual positive-half Gaussian moment relative to the original half-integer Gamma value. [GaussianGammaHalfIntegerValues](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfIntegerValues.lean) gives its exact factorial coefficient relative to Gamma at one half. [GaussianOddSymmetricQuadrature](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianOddSymmetricQuadrature.lean) checks exact finite symmetric cancellation for the literal odd Gaussian quadrature. [GaussianGammaHalfPositiveRoot](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfPositiveRoot.lean) identifies the original value at one half as a positive real square root of the exact arctangent name for pi. [GaussianGammaHalfSqrtPi](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfSqrtPi.lean) checks its equality with an independent dyadic square-root program. [GaussianGammaHalfWallisConvergence](Lean/IPRADerivations/Analysis/Stirling/Wallis/GaussianGammaHalfWallisConvergence.lean) proves the one-sided Wallis rate. [GaussianGammaHalfSqrtValues](Lean/IPRADerivations/Analysis/Gamma/HalfInteger/GaussianGammaHalfSqrtValues.lean) identifies the actual positive half-integer Gamma values and the positive-half even Gaussian moments with the independent square-root sampler and their exact factors. [GaussianEvenMomentSymmetricGrid](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianEvenMomentSymmetricGrid.lean) checks the original reflected even rows and their finite sums. [GaussianEvenMomentWholeLine](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianEvenMomentWholeLine.lean) uses the original cofinal endpoints and omitted-tail bounds for both halves. [GaussianEvenMomentWholeLineValue](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianEvenMomentWholeLineValue.lean) identifies the actual whole-line even moment with the unhalved factorial and independent square-root factors. [GaussianOddMomentWholeAbsolute](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianOddMomentWholeAbsolute.lean) gives the literal odd absolute convergence to twice the positive-half Euler reference, with exact symmetric cancellation of the signed quadrature. [GaussianOddMomentIndependentCuts](Lean/IPRADerivations/Analysis/Integration/Moments/GaussianOddMomentIndependentCuts.lean) proves the signed limit is zero at independent left and right cutoffs. Gamma-density normalization and moments are checked. [GaussianEulerIntegerMomentIntegrand](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/Moments/GaussianEulerIntegerMomentIntegrand.lean) proves the original weighted Euler row identity at every internal integer order. [GaussianGammaDensityDomain](Lean/IPRADerivations/Analysis/Gamma/Distributions/GaussianGammaDensityDomain.lean) derives the shifted integral and Gamma guards. [GaussianEulerIntegerMomentUniform](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/Moments/GaussianEulerIntegerMomentUniform.lean) gives a uniform compact clock for the literal weighted rows. [GaussianGammaDensityMomentReference](Lean/IPRADerivations/Analysis/Gamma/Distributions/GaussianGammaDensityMomentReference.lean) evaluates the normalized original shifted integral as the rising product. [GaussianEulerIntegerMomentGrid](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/Moments/GaussianEulerIntegerMomentGrid.lean) and [GaussianGammaDensityMomentGrid](Lean/IPRADerivations/Analysis/Gamma/Distributions/GaussianGammaDensityMomentGrid.lean) bind the literal weighted rows to the normalized cofinal sampler. [GaussianGammaDensityMomentName](Lean/IPRADerivations/Analysis/Gamma/Distributions/GaussianGammaDensityMomentName.lean) proves the original density moments for every internal nonnegative integer on the encoded half-plane. [GaussianGammaDensityMeanVariance](Lean/IPRADerivations/Analysis/Gamma/Distributions/GaussianGammaDensityMeanVariance.lean) gives normalization, mean and variance for that same sampler. [GaussianNamedGoldenRatio](Lean/IPRADerivations/Analysis/Names/GoldenRatio/GaussianNamedGoldenRatio.lean) proves the independent positive golden-ratio name satisfies its quadratic identity. [GaussianNamedGoldenRatioFormula](Lean/IPRADerivations/Analysis/Names/GoldenRatio/GaussianNamedGoldenRatioFormula.lean) binds that sampler to the original affine square-root expression, and [GaussianNamedGoldenRatioUniqueness](Lean/IPRADerivations/Analysis/Names/GoldenRatio/GaussianNamedGoldenRatioUniqueness.lean) proves uniqueness of its quadratic among certified positive regular names. [GaussianNamedGammaFirstCrossing](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianNamedGammaFirstCrossing.lean) proves the first Gamma crossing at three halves. [GaussianNamedGammaBackwardIdentification](Lean/IPRADerivations/Analysis/Gamma/Names/Continuation/GaussianNamedGammaBackwardIdentification.lean) identifies the original named backward argument with the literal pole-free evaluator at decoded native observations. [GaussianNamedGammaSecondCrossing](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianNamedGammaSecondCrossing.lean) proves the second crossing exactly at the independent positive golden ratio. [GaussianNamedGammaSecondCrossingWitness](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianNamedGammaSecondCrossingWitness.lean) proves the literal golden name is admitted and attains the crossing. [GaussianArctangentCayleyValues](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyValues.lean) proves the exact norm and endpoints of the rational Cayley grid. [GaussianArctangentCayleyStep](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyStep.lean) bounds its linear exponential step defect by `2/M²`. [GaussianArctangentExponentialPrefix](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/PartialSums/GaussianArctangentExponentialPrefix.lean) matches the exact arctangent prefix to the original π program. [GaussianArctangentCayleyExponentialStep](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyExponentialStep.lean) and [GaussianArctangentCayleyBudget](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyBudget.lean) give the local exponential defect and mesh budget. [GaussianArctangentQuarterExponential](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentQuarterExponential.lean) and [GaussianArctangentExponentialPeriod](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentExponentialPeriod.lean) transport the finite endpoint estimate to the original exponential clocks. [GaussianArctangentCayleyTelescope](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/Cayley/GaussianArctangentCayleyTelescope.lean) proves the finite Cayley estimate at every prefix, and [GaussianArctangentOriginalExponential](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentOriginalExponential.lean) proves the exact quarter, half and full turns for the original arctangent name. [GaussianArctangentNamedSine](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentNamedSine.lean) proves the period and signed integer zeros of the named sine, and [GaussianArctangentNamedPhase](Lean/IPRADerivations/Analysis/Trigonometry/Arctangent/GaussianArctangentNamedPhase.lean) identifies the actual integer and quarter products with the corresponding phase programs. [GaussianNamedGammaFactorialInterpolation](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/Factorials/GaussianNamedGammaFactorialInterpolation.lean) gives an explicit regular name for the alternative interpolation on the certified right half-plane, its recurrence and factorial values, and its distinction at one quarter for any nonzero rational coefficient. [GaussianGammaPoleFreeSineInterpolation](Lean/IPRADerivations/Analysis/Gamma/Poles/GaussianGammaPoleFreeSineInterpolation.lean) proves the same interpolation program satisfies the recurrence on encoded Gaussian rationals off the original poles, deriving both separation certificates from exact pole exclusion. [GaussianNamedSineTaylor](Lean/IPRADerivations/Analysis/Trigonometry/GaussianNamedSineTaylor.lean) identifies the sine factor with its literal signed factorial series at independent precisions. |

In particular, a finite factor bound or a generic exponentiation/logarithm
interface does not prove a source assertion identifying the completed named
function. A supplied final approximation certificate would be a conditional
consumer; constructing that certificate for the actual evaluator remains
part of the task.

## Positive critical point and the original named derivative

The named positive digamma is the first logarithmic Euler integral times the
certified reciprocal of the original Gamma. Its zero is equivalent to a zero
of the first Euler derivative. The two original evaluation programs can be
compared to literal rational evaluations read at a common late observation.
At the selected positive offset an explicit nonzero dyadic increment meets the
original derivative source at each precision, and its original quotient has
leading error at most `2^{-p}` from zero.
[GaussianNamedPositiveDigamma](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianNamedPositiveDigamma.lean), [GaussianGammaPositiveNamedRationalFreeze](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianGammaPositiveNamedRationalFreeze.lean), [GaussianGammaDigammaLocationGammaDerivative](Lean/IPRADerivations/Analysis/Gamma/Digamma/CriticalPoints/GaussianGammaDigammaLocationGammaDerivative.lean).

The recurrence gives a strict rational digamma lower slope across arbitrary
positive encodings with a common upper bound. Its inverse bounds the exact
input separation from independent output observations. Freezing the original
named reciprocal and Euler derivative together transports the bound to regular
positive real names. The original derivative vanishes precisely at the
selected location, under arbitrary independently chosen positive margins.
[GaussianGammaDigammaCompactSlopeLower](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaCompactSlopeLower.lean), [GaussianRationalLowerSlopeDistance](Lean/IPRADerivations/Analysis/Inequalities/GaussianRationalLowerSlopeDistance.lean), [GaussianGammaDigammaCompactInverseSlope](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaCompactInverseSlope.lean), [GaussianGammaPositiveNamedReciprocalFrozen](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianGammaPositiveNamedReciprocalFrozen.lean), [GaussianGammaPositiveNamedDigammaFrozen](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianGammaPositiveNamedDigammaFrozen.lean), [GaussianGammaPositiveNamedDigammaInjective](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianGammaPositiveNamedDigammaInjective.lean), [GaussianNamedPositiveDigammaProperness](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianNamedPositiveDigammaProperness.lean), [GaussianGammaPositiveNamedCritical](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaPositiveNamedCritical.lean).

The original positive digamma is equivalent to a name with exact real
observations. The quantitative rational upper bound controls late finite
observations whose order differs from the named input order by observation
error. This gives exact strict monotonicity on the named positive domain.
[GaussianGammaDigammaCompactLipschitz](Lean/IPRADerivations/Analysis/Gamma/Digamma/Comparison/GaussianGammaDigammaCompactLipschitz.lean), [GaussianNamedPositiveDigammaReal](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianNamedPositiveDigammaReal.lean), [GaussianGammaPositiveNamedDigammaOrder](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianGammaPositiveNamedDigammaOrder.lean).

The two original normalized Euler digamma names at a positive real input
and its unit shift satisfy the digamma recurrence. A common frozen
positive rational observation gives the literal shift with a shared
denominator. The positive margin supplies a reciprocal certificate
for the original input. The comparison rate removes the observation
errors from both digamma terms and the reciprocal.
[GaussianGammaPositiveNamedDigammaRecurrenceInput](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianGammaPositiveNamedDigammaRecurrenceInput.lean), [GaussianGammaPositiveNamedDigammaRecurrence](Lean/IPRADerivations/Analysis/Gamma/Digamma/PositiveNames/GaussianGammaPositiveNamedDigammaRecurrence.lean).

For every internal derivative order `m ≥ 1`, the literal signed
polygamma tail on a certified Gaussian-rational disk satisfies the
C30 bound `(m−1)! · 2^(m+1) / N^m`. The cutoff meets `N ≥ 2R` and
`N ≥ 1` and the finite last index is arbitrary. The proof computes
the reciprocal powers of the actual translated numerator and keeps
their original signed factorial scaling.
[GaussianGammaPolygammaTailRows](Lean/IPRADerivations/Analysis/Gamma/Digamma/Polygamma/GaussianGammaPolygammaTailRows.lean), [GaussianGammaPolygammaTail](Lean/IPRADerivations/Analysis/Gamma/Digamma/Polygamma/GaussianGammaPolygammaTail.lean).

The C29 regular series evaluator uses the literal signed prefix from
the zeroth term, with a primitive-recursive cofinal cutoff. The pole
certificate excludes zero denominators at every index. Its comparison
with any admissible cutoff retains the C30 bound and the dyadic
observation error. Identifying the series with the corresponding
derivative remains open.
[GaussianGammaPolygammaPrefix](Lean/IPRADerivations/Analysis/Gamma/Digamma/Polygamma/GaussianGammaPolygammaPrefix.lean), [GaussianGammaPolygammaSeriesName](Lean/IPRADerivations/Analysis/Gamma/Digamma/Polygamma/GaussianGammaPolygammaSeriesName.lean).

## Real Gamma away from the poles

A single late sample of a real pole-free input gives a positive margin or
a computed negative interval chart. In the negative case the two adjacent
pole separations certify a regular offset, and the literal affine shift
recovers the original input. The positive and negative quotient transfers
both preserve the caller's original reciprocal of the increment. One
computed demand supplies both derivative guards and preserves the pole
separation of the perturbed input.
[GaussianGammaNamedHalfPlanePoleFree](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedHalfPlanePoleFree.lean), [GaussianGammaNamedHalfPlanePoleFreeQuotient](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedHalfPlanePoleFreeQuotient.lean), [GaussianGammaNamedPoleFreePositiveAdmission](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreePositiveAdmission.lean), [GaussianGammaNamedPoleFreeNegativeSnapshot](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeNegativeSnapshot.lean), [GaussianGammaNamedPoleFreeRealAdmission](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeRealAdmission.lean), [GaussianGammaNamedPoleFreeNegativeChartDerivative](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeNegativeChartDerivative.lean), [GaussianGammaNamedPoleFreeIncrementSource](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeIncrementSource.lean), [GaussianGammaNamedRealDerivativeDemand](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianGammaNamedRealDerivativeDemand.lean).

The sign of the same late observation selects the derivative program,
using a fixed branch for every subsequent observation. For an arbitrary
regular real increment with a reciprocal certificate and the computed
smallness bound, the actual pole-free quotient has an independent-clock
rate to this derivative. A nonzero dyadic increment meets the demand
at each precision. The derivative is zero exactly at the selected
positive location or the selected offset in the computed negative chart.
[GaussianNameBranch](Lean/IPRADerivations/Analysis/Names/GaussianNameBranch.lean), [GaussianGammaNamedRealDerivativeStep](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianGammaNamedRealDerivativeStep.lean), [GaussianGammaNamedRealDerivative](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianGammaNamedRealDerivative.lean), [GaussianGammaNamedRealCritical](Lean/IPRADerivations/Analysis/Gamma/Names/PositiveAxis/GaussianGammaNamedRealCritical.lean).

A shared explicit dyadic increment meets the demands at two equivalent
inputs. Their original pole-free quotients agree under independent radius
and pole-separation certificates. Combining the two rates gives exact
extensionality of the derivative. On the positive domain, equality with
the selected minimum value excludes every finite apartness witness,
so the input name is equivalent to the selected minimizer.
[GaussianNamedDyadicIncrement](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedDyadicIncrement.lean), [GaussianGammaNamedPoleFreeQuotientProperness](Lean/IPRADerivations/Analysis/Gamma/Names/PoleFree/GaussianGammaNamedPoleFreeQuotientProperness.lean), [GaussianGammaNamedRealDerivativeProperness](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianGammaNamedRealDerivativeProperness.lean), [GaussianGammaMinimumGlobalUniqueness](Lean/IPRADerivations/Analysis/Gamma/CriticalPoints/PositiveMinimum/GaussianGammaMinimumGlobalUniqueness.lean).

## The right-half-plane logarithm and finite Euler heads

For a rational input with positive real numerator and positive common
denominator, the actual radial program reads half the logarithm of the
squared modulus. Its exponential agrees with an independent dyadic
square-root program. The signed phase uses the arctangent on the unit
interval and the reciprocal chart beyond it. Equal ratios give exactly
equivalent phase names. The combined logarithm has the positive-axis
readback and positive rational scaling formula of the source.
[GaussianNamedHalf](Lean/IPRADerivations/Analysis/Names/GaussianNamedHalf.lean), [GaussianPositiveRationalHalfLogarithm](Lean/IPRADerivations/Analysis/Logarithm/PositiveAxis/GaussianPositiveRationalHalfLogarithm.lean), [GaussianRightHalfPlaneRadialLogarithm](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneRadialLogarithm.lean), [GaussianRightHalfPlaneArgument](Lean/IPRADerivations/Analysis/RationalArithmetic/Complex/GaussianRightHalfPlaneArgument.lean), [GaussianRightHalfPlaneArgumentProperness](Lean/IPRADerivations/Analysis/RationalArithmetic/Complex/GaussianRightHalfPlaneArgumentProperness.lean), [GaussianRightHalfPlaneArgumentAxis](Lean/IPRADerivations/Analysis/RationalArithmetic/Complex/GaussianRightHalfPlaneArgumentAxis.lean), [GaussianRightHalfPlaneLogarithm](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithm.lean).

The small-chart phase exponential has the exact Cayley square and
nonnegative real part at every observation. Both reciprocal and
conjugate charts have explicit exponential transfer.
[GaussianRightHalfPlaneArgumentExponential](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneArgumentExponential.lean), [GaussianRightHalfPlaneArgumentCosine](Lean/IPRADerivations/Analysis/Trigonometry/GaussianRightHalfPlaneArgumentCosine.lean), [GaussianRightHalfPlaneArgumentExponentialBranches](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneArgumentExponentialBranches.lean).

In the direct phase chart, the positive radial representative times
the original phase exponential recovers the exact encoded fraction.
Their product squared is the square of the input. The finite real
margin of the sum licenses original reciprocal cancellation,
which selects the desired square root.
[GaussianNamedSquareBranch](Lean/IPRADerivations/Analysis/Names/GaussianNamedSquareBranch.lean), [GaussianRightHalfPlaneExponentialMargin](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneExponentialMargin.lean), [GaussianRightHalfPlaneExponentialSmall](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneExponentialSmall.lean).

The reciprocal phase chart follows by interchanging the numerator
magnitudes and applying the exact quarter turn to the conjugate
exponential. Conjugation then implements the negative imaginary
sign. The exponential of the full logarithm recovers the same
signed fraction program used in the original finite Euler heads
at every admitted encoded Gaussian rational.
[GaussianRightHalfPlaneExponentialCharts](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneExponentialCharts.lean), [GaussianRightHalfPlaneLogarithmExponential](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneLogarithmExponential.lean).

A common precision computed from the number of terms gives a regular
sum of the actual shifted logarithms. This yields the finite Euler head
`log(N!) + z log(N) − Σ Log(z+k)` on the rational right half-plane.
The cofinal limit and its exponential identity with the original
Gamma evaluator are constructed below.
[GaussianNamedFiniteSumFamily](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamily.lean), [GaussianLogGammaEulerHead](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerHead.lean).

Common positive rescaling of both numerators and the denominator
preserves the complete logarithm name. For any internal positive
integer `k`, the same program satisfies
`Log(z+k) = log(k) + Log(1+z/k)` with the original sign bit and
the exact shifted numerator and residual denominator.
[GaussianRightHalfPlaneLogarithmRescale](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmRescale.lean).

Finite sums of regular names now have checked first-row and final-row
splits, transport under bounded row equivalence, and additivity.
These statements compare the actual count-dependent samplers at
independent observation clocks.
[GaussianNamedFiniteSumFamilySplit](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilySplit.lean), [GaussianNamedFiniteSumFamilyCongruence](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilyCongruence.lean), [GaussianNamedFiniteSumFamilyAdd](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilyAdd.lean).

For every positive internal cutoff `N`, the same finite Euler head has
the value `z log(N) − (Log(z) + Σ_{k=1}^N Log(1+z/k))` at
independent observation clocks. An internal finite sum of the integer
logarithms equals `log(N!)`, which cancels after splitting each
denominator row. The bounded prefix and interval split reads the exact
original row at its offset.
[GaussianLogGammaFactorialLogSum](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaFactorialLogSum.lean), [GaussianLogGammaEulerFactorSum](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerFactorSum.lean), [GaussianLogGammaEulerNormalizedHead](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerNormalizedHead.lean), [GaussianNamedFiniteSumFamilyRange](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilyRange.lean).

On the signed rational disk `|w| ≤ 1/8`, the actual canonical logarithm
of `1+w` equals the actual Mercator logarithm at independently chosen
precisions. Both logarithms exponentiate to the same encoded rational.
The late difference samples have norm at most `3/4`, where the
quadratic exponential remainder gives an internal uniqueness proof.
[GaussianFiniteExponentialLocalUniqueness](Lean/IPRADerivations/Analysis/Exponential/GaussianFiniteExponentialLocalUniqueness.lean), [GaussianNamedExponentialLocalUniqueness](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedExponentialLocalUniqueness.lean), [GaussianRightHalfPlaneLogarithmMercator](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmMercator.lean).

The exact difference between two finite Euler heads is the weighted
positive-real logarithm difference minus the sum of the canonical
residual logarithms on the intervening interval. Given a bound `R`
for `|z|`, a row at `k ≥ 8R` differs from its linear term `z/k`
by at most `R²/k²` plus its explicit observation error. The linear
terms sum exactly to `z(H_{N+r}−H_N)`, which also approximates
`z(log(N+r)−log(N))` with error `R/N` plus its observation error.
[GaussianLogGammaEulerNormalizedDifference](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerNormalizedDifference.lean), [GaussianLogGammaEulerResidualCanonicalError](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerResidualCanonicalError.lean), [GaussianLogGammaEulerLinearInterval](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerLinearInterval.lean), [GaussianLogGammaEulerWeightedIntervalError](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerWeightedIntervalError.lean).

For any independently chosen observation precisions, the original Euler
heads at `N+r` and `N` differ by at most `(R²+R)/N` plus the two
observation errors when `N ≥ max(1,2R)`. The residual sum uses the
original count-dependent sampler, which absorbs its row count into the
observation precision. A primitive-recursive schedule gives a regular
cofinal name, independent of the chosen admissible radius. The concrete
radius `A+B` covers every signed rational admitted by the original
right-half-plane certificate. The half-disk branch proof below gives
the source threshold `N ≥ 2R`.
[GaussianLogGammaEulerResidualInterval](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerResidualInterval.lean), [GaussianLogGammaEulerHeadGap](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerHeadGap.lean), [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerCofinal.lean).

Exponentiating the negative of either finite Euler logarithm head
gives the original reciprocal Euler head at independently chosen
precisions. The proof identifies each shifted signed rational factor,
uses the original integer logarithm in the weighted exponent, and
folds the exponential product at every internal finite length.
[GaussianLogGammaEulerExponentialHead](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialHead.lean), [GaussianLogGammaEulerExponentialFold](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialFold.lean).

The actual exponential of the canonical cofinal log-Gamma equals the
original Gamma sampler at every admitted signed Gaussian rational.
The reciprocal identity uses the original C7 name and the pole margin
`1/D`. The checked cofinal values agree across any two presentations
with equal canonical rational arguments, including distinct sign bits
for a zero imaginary part.
[GaussianLogGammaEulerRepresentation](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerRepresentation.lean), [GaussianLogGammaEulerExponentialLimit](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialLimit.lean).

The original finite head satisfies the exact unit shift with correction
`Log(z)+log(N)−Log(z+N+1)`, after factorial cancellation and
reindexing the denominator sum. With `S` bounding `|z+1|` and
`N ≥ 8S`, the terminal observation differs from the integer logarithm
by at most `2S/N` plus a dyadic observation error. A common computed
cutoff proves `L(z+1)−L(z)=Log(z)` for the canonical cofinal names
at independent precisions.
[GaussianLogGammaEulerRecurrenceFinite](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Recurrence/GaussianLogGammaEulerRecurrenceFinite.lean), [GaussianLogGammaEulerTerminalShiftError](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Recurrence/GaussianLogGammaEulerTerminalShiftError.lean), [GaussianLogGammaEulerRecurrence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Recurrence/GaussianLogGammaEulerRecurrence.lean).

At `z=1`, the original denominator sum equals `log((N+1)!)`.
The finite Euler logarithm is therefore `log(N)−log(N+1)` and
converges to zero. This normalizes the canonical log-Gamma at every
encoding of the rational one. The positive exponential of each finite
head also equals the original finite Gamma inverse on its pole-safe
domain.
[GaussianLogGammaEulerNormalization](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerNormalization.lean), [GaussianLogGammaEulerExponentialFiniteGamma](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialFiniteGamma.lean).

The finite Euler expression for the complex slope uses the original
integer logarithm and the literal reciprocal sum through index `N`.
For positive indices, each reciprocal differs from the corresponding
harmonic term by at most `R/k²` on a certified right-half-plane input.
[GaussianLogGammaEulerReciprocalSlope](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerReciprocalSlope.lean).

Summing the reciprocal-row error and comparing it with the actual
integer-logarithm increment gives an Euler slope tail of `(R+1)/N`
at every positive cutoff. A primitive-recursive cofinal slope name
has this convergence rate with independent observation errors on the
signed rational right half-plane. Its Taylor comparison with the canonical logarithm is proved below.
[GaussianLogGammaEulerReciprocalSlopeGap](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerReciprocalSlopeGap.lean), [GaussianLogGammaEulerReciprocalSlopeCofinal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerReciprocalSlopeCofinal.lean).

The difference of the two original finite log-Gamma heads at a common
cutoff is the displacement times the original integer logarithm minus
the sum of the original shifted logarithm increments. Each relative
step has an exact reciprocal expression and a checked quadratic
Mercator observation error. Its exponential, multiplied by the base
argument, recovers the later rational argument. Coordinate and chart
ratio bounds come from the same native displacement.
[GaussianLogGammaEulerArgumentIncrement](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerArgumentIncrement.lean), [GaussianRightHalfPlaneLogarithmRelativeStep](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmRelativeStep.lean), [GaussianRightHalfPlaneLogarithmRelativeExponential](Lean/IPRADerivations/Analysis/Exponential/RightHalfPlane/GaussianRightHalfPlaneLogarithmRelativeExponential.lean).

The canonical logarithm agrees with the original Mercator logarithm
on the closed signed rational disk `|w| ≤ 1/2`. The proof bounds the
original radial name using the harmonic rectangle sums and selects the
logarithm by the fourth-root separation estimate. The same Euler
residual sampler now has its quadratic bound as soon as `k ≥ 2R`.
[GaussianRightHalfPlaneLogarithmHalfDiskBound](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmHalfDiskBound.lean), [GaussianLogGammaEulerResidualHalfDisk](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Convergence/GaussianLogGammaEulerResidualHalfDisk.lean), [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerCofinal.lean).

The canonical positive-rational observations lie on the real axis.
Their exponential is the original positive Gamma, so real
exponential injectivity identifies them with the existing real
log-Gamma evaluator for either sign encoding of zero imaginary part.
The finite linear rows also sum to the exact displacement times the
original reciprocal sum. The squared row errors have a uniform finite
majorant, with the observation errors counted explicitly.
[GaussianLogGammaEulerPositiveAxis](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerPositiveAxis.lean), [GaussianLogGammaEulerLinearSlope](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerLinearSlope.lean), [GaussianLogGammaEulerTaylorMajorant](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerTaylorMajorant.lean).

For two sufficiently close signed rational inputs on the certified
right half-plane, the actual difference of their canonical logarithms
equals the relative Mercator name. The argument charts agree at unit
ratio, and the radial and angular comparisons keep the corrected name
inside the exponential uniqueness radius. At row `k`, the original
logarithm increment differs from its linear reciprocal term by at most
`4H²/(A+kD)²` plus its common-clock dyadic observation allowance.
[GaussianRightHalfPlaneArgumentContinuity](Lean/IPRADerivations/Analysis/Names/Rates/RightHalfPlane/GaussianRightHalfPlaneArgumentContinuity.lean), [GaussianRightHalfPlaneRadialContinuity](Lean/IPRADerivations/Analysis/Names/Rates/RightHalfPlane/GaussianRightHalfPlaneRadialContinuity.lean), [GaussianRightHalfPlaneLogarithmIncrement](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmIncrement.lean).

At every positive internal cutoff, the original finite Euler
logarithm increment differs from the actual displacement times the
finite slope by at most `4H²(K²+2)/D²+25/2^p` at common precision
`p`. Here `H` bounds the native displacement, `D` is the common
denominator, and `K` bounds the reciprocal real margin. The observation
allowance is uniform in the cutoff. A computed admission from the two
real margins and the common size bound supplies the local logarithm
guards for sufficiently small displacements.
[GaussianLogGammaEulerTaylorRows](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerTaylorRows.lean), [GaussianLogGammaEulerTaylorFinite](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerTaylorFinite.lean), [GaussianRightHalfPlaneLogarithmIncrementMargin](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmIncrementMargin.lean).

The same quadratic bound holds for the cofinal logarithm increment
and the displacement times the cofinal reciprocal slope. Both original
observation precisions are independent. The uniform theorem uses a
common real margin, a common size bound and an explicit displacement
threshold. For a nonzero displacement, the native integer square root
provides positive lower and upper norm margins and a checked bound on
the actual reciprocal.
[GaussianLogGammaEulerTaylorCofinal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerTaylorCofinal.lean), [GaussianLogGammaEulerTaylorUniform](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerTaylorUniform.lean), [GaussianLogGammaEulerStepReciprocal](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerStepReciprocal.lean).

The actual punctured difference quotient is the canonical cofinal
logarithm increment multiplied by the computed rational reciprocal.
The displacement cancels against the weighted cofinal slope. The
quotient is within `8H(K²+2)/D + 2⁻ᵖ + 2⁻ᑫ` of the regular C27 series name
`−γ − 1/z + Σₖ₌₁^∞ (1/k − 1/(z+k))` at independent observation precisions
`p` and `q`. Here `D` is the common positive denominator, `H` the computed
integer radius of the displacement numerator, and `K` bounds the reciprocal
real margin. The literal finite series has a leading cutoff error of
`(R+2)/N` for every positive cutoff `N`. The closed derivative modulus
uses `8H(K²+2)2ʳ ≤ D` to obtain a leading error of `2⁻ʳ`.
[GaussianLogGammaEulerDerivativeQuotient](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerDerivativeQuotient.lean), [GaussianLogGammaEulerDigammaFractionsRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerDigammaFractionsRate.lean), [GaussianLogGammaEulerDigammaFractionsCofinal](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerDigammaFractionsCofinal.lean), [GaussianLogGammaEulerDigammaDerivative](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerDigammaDerivative.lean).

For a regular complex name with a certified positive real margin
`1/M`, the actual retimed observations admit a signed rational chart
with real part at least `1/(2M)` and a single computed disk bound.
The chart decoding preserves the exact value of each observation,
including comparisons between observations with different denominators.
[GaussianNamedRightHalfPlaneSigned](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlaneSigned.lean).

On a common positive real margin `1/K`, the actual finite complex
reciprocal sums have variation bounded by `(K²+2)|z-w|` across rational
representations with independent denominators. The same leading bound
holds for the cofinal Euler slope and the C27 digamma series, with one
dyadic error for each independently chosen output observation. Retiming
the actual input observations gives a regular digamma name on the
certified right half-plane. Equivalent input names on a common margin
and disk give equivalent digamma names.
[GaussianLogGammaEulerSlopeContinuity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerSlopeContinuity.lean), [GaussianLogGammaEulerDigammaContinuity](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerDigammaContinuity.lean), [GaussianLogGammaEulerNamedDigamma](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerNamedDigamma.lean).

The shared evaluator lift allocates half of each observation error to
retiming the input and half to evaluating at the resulting rational
chart. It proves the exact independent rate to the rational evaluator
at any sufficiently late input observation.
[GaussianNamedRightHalfPlaneLift](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlaneLift.lean).

Two independently retimed samples of regular names with a common
real margin can be placed over their literal product denominator.
The common charts preserve both values and both disk bounds. The native
displacement radius is bounded by twice the distance bound times this
denominator, including at zero for the continuity radius. For distinct
samples under the explicit local guard, the quotient of their rational
log-Gamma names has leading error `16P(K²+2)/Q` to the original digamma
partial fractions at the base sample, where `P/Q` bounds their distance
and `K=2M` bounds the reciprocal real margin of the samples.
[GaussianLogGammaEulerCommonDenominator](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerCommonDenominator.lean), [GaussianLogGammaEulerSampleDigamma](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerSampleDigamma.lean).

The named digamma program agrees with the C27 series when the input
is an admissible constant name for a signed rational. The same program
has an independent comparison with a series evaluated at any sufficiently
late original input observation, with leading error `2⁻ˢ` for the verified
freeze clock at precision `s`.
[GaussianLogGammaEulerNamedDigammaRational](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerNamedDigammaRational.lean).

The original cofinal slope is uniformly bounded on each certified
rational disk and real margin. This gives a local modulus for the
cofinal log-Gamma program via the checked quadratic estimate. Exact
rescaling of the finite shifted logarithm rows preserves the original
cofinal value, so the proof applies to observations with independent
denominators. The resulting named evaluator is regular, is proper on
each common certified domain and has the independent `2⁻ˢ` freeze rate
to its original rational program.
[GaussianLogGammaEulerReciprocalSlopeBound](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Derivatives/GaussianLogGammaEulerReciprocalSlopeBound.lean), [GaussianLogGammaEulerRationalContinuity](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerRationalContinuity.lean), [GaussianLogGammaEulerRescale](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerRescale.lean), [GaussianLogGammaEulerNamed](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerNamed.lean).

Every original right-half-plane rational chart also gives a certified
constant complex name. Its real margin is the reciprocal of the positive
integer denominator, and the theorem supplies the decoded chart certificate
at the common sample margin.
[GaussianNamedRightHalfPlaneConstant](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlaneConstant.lean).

The actual exponential of the named log-Gamma program agrees with
the original complex Gamma evaluator on the certified right half-plane.
A common late observation gives the rational exponential identity,
and a radius bound and the original evaluator clocks remove the freeze
error. The same equality holds with the general pole-free Gamma program
on their common certified domain.
[GaussianNamedRadiusExponentialFreeze](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedRadiusExponentialFreeze.lean), [GaussianLogGammaEulerExponentialFrozen](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerExponentialFrozen.lean), [GaussianLogGammaEulerNamedExponential](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Exponentiation/GaussianLogGammaEulerNamedExponential.lean).

For regular complex inputs on a common certified disk and real margin,
the actual named log-Gamma increment has a quadratic comparison with
the named displacement times the named digamma. If `P/Q` bounds the
input distance and satisfies the explicit local admission inequality,
the leading output error is `16P²(K²+2)/Q²` with `K=2M`. A computed
finite sample removes the auxiliary freeze error, leaving independent
dyadic observation errors. The comparison includes coincident inputs.
[GaussianNamedLogGammaTaylorFrozen](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianNamedLogGammaTaylorFrozen.lean), [GaussianNamedLogGammaTaylorEstimate](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianNamedLogGammaTaylorEstimate.lean).

For apart inputs, the actual log-Gamma quotient uses the verified
named reciprocal of their displacement. It converges to the named
digamma with leading error `192P(K²+2)/Q`, independent of the supplied
apartness witness. A bounded search finds the earliest witness, giving
a reciprocal bound comparable to the displacement. Witness equivalence
transfers the result back to the original quotient program. In
particular `192P(K²+2)2ʳ ≤ Q` suffices for leading error `2⁻ʳ`.
[GaussianNamedTaylorDifferenceQuotient](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNamedTaylorDifferenceQuotient.lean), [GaussianNamedMinimumApartness](Lean/IPRADerivations/Analysis/Names/Apartness/GaussianNamedMinimumApartness.lean), [GaussianNamedLogGammaDerivativeUniform](Lean/IPRADerivations/Analysis/Gamma/Names/Derivatives/GaussianNamedLogGammaDerivativeUniform.lean).

On positive rational inputs, the literal complex digamma series
agrees with the original real `Γ′/Γ` evaluator. The finite formulas
differ by one terminal reciprocal, which is bounded by `1/N`.
For every certified positive real name, a shared late observation
then identifies the two actual named evaluators. The comparison with
the original `Γ′/Γ` programs at nonreal inputs remains open.
[GaussianLogGammaEulerDigammaPositiveAxis](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerDigammaPositiveAxis.lean), [GaussianLogGammaEulerNamedDigammaPositiveAxis](Lean/IPRADerivations/Analysis/Gamma/Digamma/LogGammaDerivative/GaussianLogGammaEulerNamedDigammaPositiveAxis.lean).

The canonical right-half-plane logarithm is also a regular named
evaluator, with a local rational modulus and a checked late-observation
rate. The named unit shift uses the actual addition clock. Its signed
rational sample is exactly the base sample with its real numerator
increased by its denominator. Exact cofinal chart agreement aligns the
two representations of that shifted sample. Comparing the three named
evaluations at the same base observation proves
`ℒ(z+1) − ℒ(z) = Log z`. The theory can compute both disk bounds directly
from the original and shifted input names.
[GaussianRightHalfPlaneLogarithmNamed](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmNamed.lean), [GaussianLogGammaEulerChartAgreement](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerChartAgreement.lean), [GaussianLogGammaEulerShiftedChart](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Recurrence/GaussianLogGammaEulerShiftedChart.lean), [GaussianLogGammaEulerNamedRecurrence](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/Recurrence/GaussianLogGammaEulerNamedRecurrence.lean).

The canonical named log-Gamma agrees with the original real log-Gamma
on every certified positive real name. At a sufficiently late real
observation, exact rational chart agreement identifies the two inputs
to the already proved positive-rational identity. This yields equality
of the actual named evaluators for every admissible disk bound.
[GaussianLogGammaEulerNamedPositiveAxis](Lean/IPRADerivations/Analysis/Gamma/EulerProducts/LogGamma/GaussianLogGammaEulerNamedPositiveAxis.lean).

For the complex digamma comparison used in the first Binet formula,
the actual reciprocal at any rational tag in a horizontal unit cell
differs from the left reciprocal by at most the adjacent difference of
positive real reciprocals. The same sharp bound holds for the literal
finite average over the tags. For a small horizontal step the original
canonical logarithm observations satisfy the quadratic estimate with
the actual rational width times the left reciprocal as linear term.
[GaussianBinetReciprocalRows](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetReciprocalRows.lean), [GaussianBinetReciprocalMean](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetReciprocalMean.lean), [GaussianBinetLogHorizontalStep](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetLogHorizontalStep.lean).

At a common horizontal unit mesh, the actual logarithm increment
approaches the literal reciprocal average. At any internal prefix
length `N`, quantifier-free induction compares the logarithm
increment to the original reciprocal sum, with leading bound
`1/Re(z) − 1/(Re(z)+N)`. The finite Euler slope shares the same
reciprocal prefix. Comparing its terminal real logarithm to the
shifted canonical logarithm and passing to the cofinal names proves
`|ψ(z)−Log(z)| ≤ 1/Re(z)` for every signed rational chart in the
right half-plane. The statement allows independent observation clocks.
[GaussianBinetLogCellGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetLogCellGrid.lean), [GaussianBinetLogCellComparison](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetLogCellComparison.lean), [GaussianBinetReciprocalPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetReciprocalPrefix.lean), [GaussianBinetDigammaLogBound](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetDigammaLogBound.lean).

The complex Stirling remainder uses the actual cofinal log-Gamma, the
canonical logarithm and the named Stirling constant. Its restriction to
the positive real axis agrees exactly with the original real remainder,
including the sharp absolute bound `1/(12x)`. The canonical recurrence
gives its exact unit difference
`R(z)−R(z+1) = (z+1/2)(Log(z+1)−Log(z))−1`.
[GaussianBinetStirlingRemainder](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingRemainder.lean), [GaussianBinetStirlingRealBound](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingRealBound.lean), [GaussianBinetStirlingUnitDifferenceAlgebra](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingUnitDifferenceAlgebra.lean), [GaussianBinetStirlingUnitDifference](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingUnitDifference.lean).

On the original uniform grid of `[0,1]`, the weighted resolvent
`(1/2−t)/(z+t)` has an exact affine reduction at every tag. Its literal
finite sum and cofinal quadrature agree with the canonical logarithm
increment expression. The resulting cofinal unit quadrature equals
the actual remainder difference `R(z)−R(z+1)`.
[GaussianBinetWeightedResolventGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedResolventGrid.lean), [GaussianBinetWeightedResolvent](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedResolvent.lean).

The actual unit grid for `(1/2−u) exp(−tu)` has a checked mesh and
observation error against the elementary endpoint primitive. At
positive rational `t`, the regular cofinal name equals
`(1+exp(−t))/(2t)−(1−exp(−t))/t²`. At zero the literal left grid of
size `N` gives `1/(2N)` and its cofinal value is zero.
[GaussianBinetWeightedExponentialAlgebra](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialAlgebra.lean), [GaussianBinetWeightedExponentialGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialGrid.lean), [GaussianBinetWeightedExponentialZero](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialZero.lean), [GaussianBinetWeightedExponential](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponential.lean).

On a bounded interval `0 ≤ t ≤ T`, the weighted exponential unit
quadrature has a time-uniform cell bound and a uniform comparison to
both finite left and midpoint grids. The left-grid error is at most
`g(T)/M + (g(T)+8)/2^p`, where `g(T)=2·3^T·T+3`. The exact one-cell
value gives a uniform bound on every original cofinal observation.
[GaussianBinetWeightedExponentialRowRate](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialRowRate.lean), [GaussianBinetWeightedExponentialUniform](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialUniform.lean), [GaussianBinetWeightedExponentialBound](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialBound.lean), [GaussianBinetWeightedExponentialMidpoint](Lean/IPRADerivations/Analysis/Stirling/Binet/WeightedIntegrals/GaussianBinetWeightedExponentialMidpoint.lean).

A literal signed vertical step has the checked quadratic logarithm
estimate. The normalized first-order Stirling expression
`ψ(z)−Log(z)+1/(2z)` has absolute bound `3/(2 Re(z))` at independent
observations.
[GaussianBinetLogVerticalStep](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetLogVerticalStep.lean), [GaussianBinetStirlingSlopeBound](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingSlopeBound.lean).

The actual vertical remainder increment has the first-order term
formed from the literal displacement and the same-clock original
digamma, logarithm and half reciprocal. Exact subtraction cancels the
common Stirling constant. The observation bound retains separate
quadratic log-Gamma and logarithm contributions and normalization
allowances for the original remainder samples.
[GaussianBinetStirlingVerticalAlgebra](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingVerticalAlgebra.lean), [GaussianBinetLogGammaVerticalStep](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetLogGammaVerticalStep.lean), [GaussianBinetStirlingVerticalStep](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingVerticalStep.lean).

The literal vertical increments telescope over an internal subdivision.
Positive rescaling identifies the subdivided endpoints with the original
remainder names. If `z = (A ± Bi)/D`, the vertical difference from `R(A/D)`
has leading norm bound `3B/(2A)`. The sharp positive-real anchor gives the
full leading bound `(D+18B)/(12A)` for `R(z)`, with an explicit error at
independent observation clocks.
[GaussianBinetStirlingRescale](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingRescale.lean), [GaussianBinetStirlingVerticalRate](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingVerticalRate.lean), [GaussianBinetStirlingVerticalGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingVerticalGrid.lean), [GaussianBinetStirlingVerticalBound](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingVerticalBound.lean).

For the imaginary-axis sine product used in the Binet kernel
identification, the actual finite factor derivative terms give the
literal derivative of the encoded product at any internal cutoff. The
exact first-order expansion uses a primitive recursive second-order
remainder and retains the original sine product at both inputs.
[GaussianSineProductImaginaryLogDerivative](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryLogDerivative.lean), [GaussianSineProductImaginaryFirstOrder](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryFirstOrder.lean).

The imaginary-axis sine-product expansion has a quadratic error
uniform in the cutoff on each bounded interval. The literal row
sum has a quantitative tail and a regular cofinal sampler. Passing
the derivative expansion to the original cofinal sine product keeps
the weighted cofinal derivative term and the exact quadratic rate
with independent observation clocks. The product and reciprocal row
names are invariant under exact rational rescaling.
[GaussianSineProductImaginaryLogDerivativeTail](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryLogDerivativeTail.lean), [GaussianSineProductImaginaryFirstOrderBound](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryFirstOrderBound.lean), [GaussianSineProductImaginaryCofinalDerivative](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryCofinalDerivative.lean), [GaussianSineProductImaginaryScaling](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryScaling.lean).

The original named exponential has a first-order remainder at any
regular small input and an independent quadratic rate for shifts.
Signed rational multiples of the original π name preserve exact
additive increments. Multiplication by the literal imaginary unit
agrees with the actual rotation name used by the sine connection.
[GaussianNamedExponentialLinearRate](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedExponentialLinearRate.lean), [GaussianNamedExponentialShiftDerivative](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedExponentialShiftDerivative.lean), [GaussianPiRationalScale](Lean/IPRADerivations/Analysis/Trigonometry/Pi/GaussianPiRationalScale.lean), [GaussianNamedImaginaryProduct](Lean/IPRADerivations/Analysis/Names/ImaginaryParts/GaussianNamedImaginaryProduct.lean).

At nonnegative rational `x` in a certified bounded interval, the
actual original exponential expression for `sinh(πx)` equals the
product of `πx` and the original cofinal sine product on the imaginary
axis. Positive rescaling preserves the original signed π inputs
exactly. A separate dyadic uniqueness theorem identifies two regular
slope names when their weighted approximants differ quadratically at
the common nonzero step.
[GaussianPiRationalScaleRepresentation](Lean/IPRADerivations/Analysis/Trigonometry/Pi/GaussianPiRationalScaleRepresentation.lean), [GaussianNamedScaledDerivativeUniqueness](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedScaledDerivativeUniqueness.lean), [GaussianSineProductImaginaryHyperbolic](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryHyperbolic.lean).

The actual hyperbolic exponential expression has a first-order rate
at a fixed rational base under a positive change of encoding. The
quadratic numerator is uniform as the rational step tends to zero.
The derivative expression equals the original named `π cosh(πx)`.
The original sine product representation has a matching independent
product-rule estimate whose quadratic coefficient is also uniform
under rescaling.
[GaussianNamedDifferenceAlgebra](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedDifferenceAlgebra.lean), [GaussianPiRationalScaleFactors](Lean/IPRADerivations/Analysis/Trigonometry/Pi/GaussianPiRationalScaleFactors.lean), [GaussianSineProductImaginaryExponentialShift](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryExponentialShift.lean), [GaussianSineProductImaginaryHyperbolicDerivative](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryHyperbolicDerivative.lean), [GaussianSineProductImaginaryCoshIdentity](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryCoshIdentity.lean), [GaussianSineProductImaginaryHyperbolicProductRuleAlgebra](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryHyperbolicProductRuleAlgebra.lean), [GaussianSineProductImaginaryHyperbolicProductRule](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryHyperbolicProductRule.lean).

At a fixed rational base `x`, the two actual derivative names are
equal by comparison at a common nonzero dyadic displacement. Cancel
the original apart π factor to get `cosh(πx) = P(x)+xD(x)` for the
cofinal sine product `P` and its actual derivative `D`.
[GaussianSineProductImaginaryDerivativeComparison](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryDerivativeComparison.lean), [GaussianSineProductImaginaryCofinalLogDerivative](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryCofinalLogDerivative.lean).

Combining that derivative with the exact hyperbolic sine identity
proves the cleared partial fractions
`(πx) cosh(πx) = sinh(πx) (1+x Σⱼ 2x/(j²+x²))` at the original
rational inputs. This uses the actual cofinal reciprocal row name.
[GaussianSineProductImaginaryCothExpansion](Lean/IPRADerivations/Analysis/Trigonometry/Hyperbolic/GaussianSineProductImaginaryCothExpansion.lean).

At a nonnegative rational time `t`, the cofinal kernel `k(t)` satisfies
`(t/2) cosh(t/2) = sinh(t/2) (1+t² k(t))` with the original exponential
names. Freezing π once at a shared observation binds the literal kernel
rows to the partial-fraction samples. The uniform bounds remove the
freeze and identify the hyperbolic factors at their original time.
[GaussianBinetKernelImaginaryRatioRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelImaginaryRatioRows.lean), [GaussianBinetKernelImaginaryRatioPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelImaginaryRatioPrefix.lean), [GaussianBinetKernelImaginaryRatioCofinal](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelImaginaryRatioCofinal.lean), [GaussianBinetKernelFrozenHyperbolic](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrozenHyperbolic.lean), [GaussianNamedUniformRateClosure](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedUniformRateClosure.lean), [GaussianBinetKernelRationalTimeCleared](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelRationalTimeCleared.lean).

For positive rational time the original hyperbolic sine is apart from zero.
Its actual Taylor series gives a quantitative lower bound from the first
odd term. Cancelling the original denominator yields
`k(t) = ((t/2) cosh(t/2)−sinh(t/2))/(t² sinh(t/2))` with the actual
reciprocal sampler. At zero the original kernel equals `1/12`.
[GaussianBinetKernelSinhOddLower](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelSinhOddLower.lean), [GaussianBinetKernelSinhApartness](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelSinhApartness.lean), [GaussianNamedClearedScalarQuotient](Lean/IPRADerivations/Analysis/Names/Apartness/GaussianNamedClearedScalarQuotient.lean), [GaussianBinetKernelElementaryRational](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelElementaryRational.lean).

Multiplying the cleared kernel identity by the original negative
half-time exponential identifies `(1−exp(−t))k(t)` with the actual
cofinal quadrature of `(1/2−u)exp(−tu)` on `[0,1]`. The positive
branch cancels an exact nonzero rational scale. At `t = 0` the
weighted grid bound proves exact agreement and regularity.
[GaussianBinetKernelHalfExponential](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelHalfExponential.lean), [GaussianBinetKernelWeightedBridge](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelWeightedBridge.lean), [GaussianBinetKernelWeightedBridgeZero](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelWeightedBridgeZero.lean).

On each bounded rational time panel, the original exponential
at `−(z+1)t` equals the product of the original names at `−zt` and
`−t`. The actual integrand difference across `z` and `z+1` therefore
equals the original `exp(−zt)` times the cofinal weighted exponential
unit quadrature. This applies to any admitted radii for the two
original integrands and includes time zero.
[GaussianBinetLaplaceExponentialShift](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceExponentialShift.lean), [GaussianBinetLaplaceIntegrandShift](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceIntegrandShift.lean), [GaussianBinetLaplaceWeightedShiftRow](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceWeightedShiftRow.lean).

The Binet kernel series uses the original named π in each positive row
`2/(t²+4π²n²)`. On `0 ≤ t ≤ T` the actual finite and cofinal samples
are bounded below by `2/(T²+100)` at positive cutoffs. The row majorant
`1/(8n²)` gives the uniform leading tail bound `1/(8N)` for every
positive cutoff `N`. The comparison of the original finite and cofinal
evaluators retains independent dyadic errors. Both evaluators satisfy
the cutoff-independent Lipschitz estimate with gain `T` on `[0,T]`,
including its uniform-mesh specialization.
[GaussianBinetKernelPi](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelPi.lean), [GaussianBinetKernelRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelRows.lean), [GaussianBinetKernelPositive](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelPositive.lean), [GaussianBinetKernelTailMajorant](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelTailMajorant.lean), [GaussianBinetKernelTail](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelTail.lean), [GaussianBinetKernelCofinal](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelCofinal.lean), [GaussianBinetKernelTimeContinuity](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelTimeContinuity.lean).

The literal reciprocal-square sum satisfies the Basel identity against
the original zeta and π names. Rewriting each actual zero-parameter
kernel row by that sum identifies the cofinal kernel at zero with
`1/12` for every positive denominator encoding. The exact finite row
order gives the global upper bound `k(t) ≤ 1/12` for nonnegative rational
`t`. A sample at clock `p` obeys the upper bound `1/12 + 2⁻ᵖ`.
[GaussianBinetBaselBinding](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetBaselBinding.lean), [GaussianBinetBaselName](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetBaselName.lean), [GaussianBinetKernelZero](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelZero.lean), [GaussianBinetKernelUpper](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelUpper.lean).

On a certified finite strip the original Gaussian exponential is
evaluated at the exact argument `−zt`. Its normalized product with
the kernel samples gives the finite and cofinal Binet integrands.
The independent observation comparison with the finite cutoff has
leading error `1/(8N)`. The integrand has a computable Lipschitz gain
uniform in the cutoff on each finite strip and a finite mesh bound.
[GaussianBinetKernelCoarseBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelCoarseBound.lean), [GaussianBinetLaplaceExponential](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceExponential.lean), [GaussianBinetLaplaceIntegrand](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceIntegrand.lean).

The original integrands yield regular compact quadrature names on
any admitted finite panel in nonnegative time. The translated chart
reads each tag at its exact physical rational time, including zero.
The arbitrary grid-refinement and same-grid cutoff comparisons give
the named compact truncation estimate with leading error
`(panel width)/(8N)` at independent observation clocks.
Changing the certified disk radius or time horizon preserves the actual
integrand at each physical tag and preserves the compact name for the
same panel.
[GaussianBinetLaplaceStrip](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStrip.lean), [GaussianBinetLaplaceStripCutoff](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStripCutoff.lean), [GaussianBinetLaplaceStripHorizon](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStripHorizon.lean).

The squared norm of the actual complex exponential at `−zt` agrees
with the square of the original real decay at `−Re(z)t`. The observation
norm estimate transfers that decay to the actual normalized product
with the kernel. The majorant retains the leading coefficient `1/12`
and explicit errors at the original product and real decay clocks.
[GaussianBinetLaplaceDecay](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceDecay.lean), [GaussianBinetLaplaceDomination](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceDomination.lean).

The compact tail after a rational endpoint is bounded uniformly in
the strip width and the certified horizon. The original nonnegative
real decay sample at the starting endpoint supplies the sharp leading
coefficient `1/(12 Re(z))`, with explicit independent observation
errors. At physical cutoff `D L`, an effective envelope gives leading
bound `D 2⁻ᴸ/(12 X)` for `Re(z)=X/D`. A zero-width strip evaluates
exactly to zero.
[GaussianBinetLaplaceScalarMajorant](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceScalarMajorant.lean), [GaussianBinetLaplaceStripDomination](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStripDomination.lean), [GaussianBinetLaplaceStripTail](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStripTail.lean), [GaussianBinetLaplaceStripTailEnvelope](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceStripTailEnvelope.lean), [GaussianBinetLaplaceSharpTail](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceSharpTail.lean).

The original compact quadrature is additive at a physical split.
The prefix comparison retains the effective leading tail
`D 2⁻ᴸ/(12 X)` at independent clocks for a prefix ending at `D L`.
This also compares two actual exhaustion prefixes at their own
horizons and covers equality of cutoffs.
[GaussianBinetLaplaceExhaustion](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceExhaustion.lean), [GaussianBinetLaplaceOrderedPrefixes](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceOrderedPrefixes.lean).

The improper Binet Laplace name reads the actual compact quadrature
at an internal cutoff and a later clock. It is regular on each
certified signed rational right-half-plane chart. Its observations
compare to those of every positive finite prefix with the same
leading bound `D 2⁻ᴸ/(12 X)`.
[GaussianBinetLaplaceImproperName](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceImproperName.lean).

The original real decay at time zero evaluates exactly to one. The
finite decay quadrature includes the zero left cell with the same
error bound. The actual improper Binet sampler consequently has
norm at most `1/(12 Re(z)) + 2⁻⁽ᵖ⁺¹⁾` at its observation clock `p`.
[GaussianEulerDecayQuadratureAtZero](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayQuadratureAtZero.lean), [GaussianBinetLaplaceImproperBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceImproperBound.lean).

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

The difference of the two actual improper observations is within
`16/2^p` of the literal difference of the compact quadratures on a
common grid. The horizon `D L` is shared and the condition
`D 2^p ≤ 2^L` absorbs both original tails. The grid can be refined
further and the row clock increased while preserving the bound.
[GaussianCompactPointwiseDifference](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactPointwiseDifference.lean), [GaussianCompactDifferenceRefinement](Lean/IPRADerivations/Analysis/Integration/CompactGrids/GaussianCompactDifferenceRefinement.lean), [GaussianBinetLaplaceDifferencePrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceDifferencePrefix.lean), [GaussianBinetLaplaceDifferenceGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceDifferenceGrid.lean).

For the original finite exponential rectangle, interchanging the two
sums leaves the actual serialized weights and observations in place.
The complex exponential columns telescope to their original endpoint
expression, and their tails decay on the selected horizon. At the
prescribed finite budgets, the rectangle is within `2/2^p` of the
literal weighted-resolvent grid. The cofinal comparison binds its
limit to the canonical Stirling unit difference.
[GaussianBinetExponentialPanel](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialPanel.lean), [GaussianBinetExponentialIntegralGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialIntegralGrid.lean), [GaussianBinetExponentialIntegral](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialIntegral.lean), [GaussianBinetExponentialRectangle](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangle.lean), [GaussianBinetExponentialRectangleShift](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangleShift.lean), [GaussianBinetExponentialRectangleColumn](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangleColumn.lean), [GaussianBinetExponentialRectangleEndpoint](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangleEndpoint.lean), [GaussianBinetExponentialRectangleResolvent](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangleResolvent.lean), [GaussianBinetExponentialRectangleEvaluation](Lean/IPRADerivations/Analysis/Stirling/Binet/ExponentialIntegrals/GaussianBinetExponentialRectangleEvaluation.lean).

The normalized discrepancy `R(z+j)−J(z+j)` uses the actual remainder and
actual improper Binet names. Its bound decays uniformly as the internal
shift `j` grows, with a separate dyadic observation allowance. An adjacent
equality proof would make that family constant and hence zero. The closed
conditional derives the first Binet identity from the hypothesis that the
actual unit difference of `J` equals the weighted-resolvent quadrature
along the entire translated family.
[GaussianNamedRecurrencePinning](Lean/IPRADerivations/Analysis/Names/GaussianNamedRecurrencePinning.lean), [GaussianNamedDifferenceZero](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedDifferenceZero.lean), [GaussianBinetFirstFormulaDecay](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormulaDecay.lean), [GaussianBinetFirstFormulaPinning](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormulaPinning.lean).

The first Binet formula is proved for the two original names at every
encoded complex rational point in the right half-plane. At each requested
precision, one explicit horizon, clock, and pair of meshes satisfy both
sides of the rectangle comparison. Their bound identifies the actual
unit difference of the improper sampler with the weighted resolvent.
The translated discrepancy argument then proves equality of the
Stirling remainder and the original improper integral. The closed
theorem has only the original input-domain guard.
[GaussianNamedProductObservationBound](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedProductObservationBound.lean), [GaussianBinetLaplaceWeightedGridReadback](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceWeightedGridReadback.lean), [GaussianBinetLaplaceWeightedGridProduct](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceWeightedGridProduct.lean), [GaussianBinetLaplaceWeightedGridRectangle](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceWeightedGridRectangle.lean), [GaussianBinetLaplaceRectangleRowBudget](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceRectangleRowBudget.lean), [GaussianBinetLaplaceRectangleSchedule](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceRectangleSchedule.lean), [GaussianBinetLaplaceRectangleJoin](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Rectangles/GaussianBinetLaplaceRectangleJoin.lean), [GaussianBinetFirstFormula](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormula.lean).

On a common right-half-plane margin and disk, the original rational
Stirling remainder has an explicit linear rate. Transferring it to
the original improper Laplace sampler gives a regular named lift
with a quantitative readback at late rational observations. A
single late rational observation identifies the lift with the
Stirling remainder assembled from the original named log-Gamma,
logarithm, argument and Stirling constant.
[GaussianRightHalfPlaneLogarithmCompactBound](Lean/IPRADerivations/Analysis/Logarithm/RightHalfPlane/GaussianRightHalfPlaneLogarithmCompactBound.lean), [GaussianBinetStirlingRemainderRate](Lean/IPRADerivations/Analysis/Stirling/Binet/StirlingBounds/GaussianBinetStirlingRemainderRate.lean), [GaussianBinetLaplaceNamed](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceNamed.lean), [GaussianBinetFirstFormulaNamed](Lean/IPRADerivations/Analysis/Stirling/Binet/GaussianBinetFirstFormulaNamed.lean).

For the second Binet formula, the original rational integrand
`z/(z²+u²)` equals the average of the two resolvents at `z±iu` on the
right half-plane. The admitted poles have the same positive-real
margin. The resulting original compact arctangent quadrature is
regular, and every actual observation at time `t` has norm bounded
by `t/Re(z)`.
[GaussianBinetArctangentResolvent](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentResolvent.lean), [GaussianBinetArctangentResolventRate](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentResolventRate.lean), [GaussianBinetArctangentQuadrature](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentQuadrature.lean), [GaussianBinetArctangentQuadratureBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentQuadratureBound.lean).

The two original exponential panel sums at the signed poles read back
on one common horizon. Their symmetric average approximates the exact
cosine resolvent uniformly over a bounded rational frequency interval,
with explicit finite-mesh and exponential-tail errors.
[GaussianBinetArctangentSignedPole](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentSignedPole.lean), [GaussianBinetArctangentPoleLaplace](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentPoleLaplace.lean), [GaussianBinetArctangentCosineLaplace](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentCosineLaplace.lean).

The original pure-imaginary exponential quadrature satisfies the
cleared finite antiderivative with both frequency signs, including
zero. The difference of the original signed-pole Laplace panels
approximates the cleared sine resolvent with uniform bounds on the
bounded frequency interval.
[GaussianBinetImaginaryExponentialIntegral](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetImaginaryExponentialIntegral.lean), [GaussianBinetSineLaplaceResolvent](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineLaplaceResolvent.lean).

On a common grid, the original finite arctangent quadrature compares
with the original rectangle of cosine transforms. The outer grid
multiplies the uniform resolvent error by its physical width. Each
actual shifted exponential factors with explicit error into the
original damping and the purely imaginary oscillatory sample.
[GaussianBinetArctangentCosineRectangle](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentCosineRectangle.lean), [GaussianBinetOscillatoryPanelFactor](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatoryPanelFactor.lean).

The actual positive Pi-scaled exponential has a Taylor gap from one
of at least `4t` at every positive rational time. Its reciprocal is
regular and has norm at most `1/(4t)` at every observation. The
original arctangent times this reciprocal has norm at most
`1/(4 Re(z))` all the way toward the origin. For an exact rational
inverse pair `xy = 1`, the literal geometric power sum has the
cleared finite identity `(x−1) Σ_{j=1}^N y^j = 1−y^N`.
[GaussianExponentialAffineLower](Lean/IPRADerivations/Analysis/Exponential/Estimates/GaussianExponentialAffineLower.lean), [GaussianBinetBoseExponential](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseExponential.lean), [GaussianBinetBoseDenominator](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseDenominator.lean), [GaussianBinetBoseIntegrandBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseIntegrandBound.lean), [GaussianRationalInverseGeometric](Lean/IPRADerivations/Analysis/Geometry/GeometricBounds/GaussianRationalInverseGeometric.lean).

The original finite cosine rectangle equals the transposed sum with
both literal mesh weights. The transposed entries have an explicit
comparison to the original damping multiplied by the mean of the
two imaginary exponentials. Exact signed rational rescaling binds
their frequency charts at the actual grid tags.
[GaussianRationalQuadratureMean](Lean/IPRADerivations/Analysis/Integration/Quadrature/GaussianRationalQuadratureMean.lean), [GaussianBinetOscillatoryRectangleTranspose](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatoryRectangleTranspose.lean), [GaussianBinetOscillatoryMatrixCell](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatoryMatrixCell.lean), [GaussianBinetImaginaryExponentialScale](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetImaginaryExponentialScale.lean).

At every original arctangent observation, the leading term is
`t/z` with norm error at most `(t/Re(z))³`. The original rational
rows retain their exact values, so this bound has no sampling
allowance. For positive rational time the divided arctangent
differs from `1/z` by at most `t²/Re(z)³`.
[GaussianBinetArctangentLinearApproximation](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentLinearApproximation.lean).

Read the positive exponential sample selected by the actual Bose
reciprocal. The exact inverse of that exponential sample has norm
at most `1/(1+4t)`. For `t=A/B>0` its literal geometric prefix of
length `N` differs from the original reciprocal observation by
at most `B²/[4A(B+4NA)]`, independently of the observation clock.
[GaussianBinetBoseGeometricRatio](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseGeometricRatio.lean), [GaussianRationalGeometricPowerTail](Lean/IPRADerivations/Analysis/Geometry/GeometricBounds/GaussianRationalGeometricPowerTail.lean), [GaussianBinetBoseSeries](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseSeries.lean).

The literal arctangent-decay row admits a common half-decay majorant
with an explicit clock allowance, including at time zero. The rescaled
zero-start scalar quadrature yields the bound `11K/m²` for row `m`
on every integer horizon with the verified mesh and clock budgets.
A shared grid and one frozen Pi sample give the actual tail bound
`11K/C` for every finite block after row `C`.
[GaussianBinetSecondDecayEnvelope](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayEnvelope.lean), [GaussianBinetSecondDecayPointwise](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayPointwise.lean), [GaussianBinetSecondDecayQuadrature](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayQuadrature.lean), [GaussianBinetSecondDecayGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayGrid.lean), [GaussianBinetSecondDecayFinite](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayFinite.lean), [GaussianBinetSecondDecayTail](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayTail.lean), [GaussianBinetSecondDecayFrozenTail](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayFrozenTail.lean).

The original unscaled second Binet integrand has the continuous
endpoint `1/(2π z)` at zero. The denominator's original observation
keeps its own Pi sample and has quadratic error from the linear
term at that clock. Comparing with the original divided arctangent
gives leading error `(K³+100K)t` for `0<t≤1/10` and
`1/Re(z)≤K`, with independent observation errors.
[GaussianBinetBoseLinearApproximation](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLinearApproximation.lean), [GaussianBinetBoseIntegrandEndpoint](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseIntegrandEndpoint.lean).

The original signed Pi-scaled decay row compares with the actual
frozen-Pi decay evaluator on the same compact time interval. Its
rate is uniform in the encoded rational tag and therefore works
across every later time mesh. The product rate also applies to
the original arctangent-weighted rows.
[GaussianBinetSecondDecayPiBridge](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayPiBridge.lean).

At each positive rational time, the corresponding original signed
exponential rows approximate the powers of the actual geometric ratio.
Their literal finite sums give a regular cofinal evaluator. Its normalized
samples read back the exact finite prefix and differ from the reciprocal
of the original Bose denominator by at most `6/2^p`. The object theory
proves equivalence of the two names.
[GaussianBinetBoseIntegerScale](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseIntegerScale.lean), [GaussianBinetBoseSeriesRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseSeriesRows.lean), [GaussianBinetBoseLiteralPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLiteralPrefix.lean), [GaussianBinetBoseLiteralCofinal](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLiteralCofinal.lean)

The original transposed cosine columns approximate the sine
quotient on the same mesh. At positive time the cleared cosine
antiderivative gives the quotient by the imaginary frequency. At
zero the regularized quotient has its exact removable value. A
single primitive-recursive row inherits uniform norm and mesh bounds.
[GaussianBinetCosinePrimitive](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetCosinePrimitive.lean), [GaussianBinetOscillatoryColumns](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatoryColumns.lean), [GaussianBinetOscillatorySineQuotient](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatorySineQuotient.lean), [GaussianBinetOscillatoryZeroColumn](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatoryZeroColumn.lean), [GaussianBinetOscillatorySineRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatorySineRows.lean)

Summing the regularized sine columns with the original time weight
gives a finite damped sine integral. It approximates both the original
finite arctangent quadrature and the original arctangent observations,
with explicit mesh, horizon and clock errors.
[GaussianBinetOscillatorySineRectangle](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatorySineRectangle.lean), [GaussianBinetArctangentSineGridComparison](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentSineGridComparison.lean)

The original second Binet product admits a compact integral on every
positive rational interval `[A/E,(A+C)/E]`. The original arctangent
and reciprocal have time rates on that interval, so the literal
left quadrature defines a regular name. Every actual sample has
norm at most `CD/(4EX)` for real part `X/D`, including intervals
whose lower endpoint tends to zero.
[GaussianBinetBoseReciprocalTimeRate](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseReciprocalTimeRate.lean), [GaussianBinetArctangentTimeRate](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentTimeRate.lean), [GaussianBinetBoseCompact](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseCompact.lean), [GaussianBinetBoseCompactBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseCompactBound.lean)

At each positive frozen Pi frequency, the exact shifted exponential
panels compare to the standard real damping times the original
regularized sine quotient. Summing on the shared mesh gives the
actual Binet kernel row, up to explicit mesh, horizon and clock
errors. Independent radii and clocks for the same positive sine
quotient have a separate quantitative comparison.
[GaussianBinetSineDampedTransform](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineDampedTransform.lean), [GaussianBinetSineFrozenPiTerm](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineFrozenPiTerm.lean), [GaussianBinetSineDampedAxis](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineDampedAxis.lean), [GaussianBinetSineDampedPanels](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineDampedPanels.lean), [GaussianBinetSineRealDampedPanels](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineRealDampedPanels.lean), [GaussianBinetSineDampedQuadrature](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineDampedQuadrature.lean), [GaussianBinetSineQuotientClock](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineQuotientClock.lean)

A single frozen Pi clock supplies every literal reciprocal row. The truncated kernel and the actual exponential-weighted prefix compare with the cofinal kernel and the original first Binet Laplace integrand, with quantitative cutoff and clock budgets.
[GaussianBinetKernelFrozenPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrozenPrefix.lean)

Exact compact rescaling and additivity compare the original intervals whose lower endpoints are dyadic. The omitted strip has norm at most its width divided by four times the real part. The resulting regular name integrates the original product from zero to each positive integer horizon.
[GaussianBinetBoseCompactAlignment](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseCompactAlignment.lean), [GaussianBinetBoseOriginExhaustion](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseOriginExhaustion.lean), [GaussianBinetBoseOriginName](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseOriginName.lean)

The original exponential-minus-one observation retains a cubic Taylor lower bound. The arctangent times the original reciprocal is bounded by K/t² when D≤KX. Its actual compact integral on [A/E,(A+C)/E] is bounded by 2KE/A with an explicit sample allowance, independently of the upper endpoint.
[GaussianBinetBoseCubicGap](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseCubicGap.lean), [GaussianBinetBoseFarBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFarBound.lean), [GaussianBinetBoseFarQuadrature](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFarQuadrature.lean)

The time margin E·t≥1 permits a common cutoff N≥E²·2^p. Each original arctangent-weighted cell of that literal prefix compares with its frozen Pi counterpart, with a common error 5KT/2^p over t≤T when D≤KX.
[GaussianBinetBoseLiteralUniform](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLiteralUniform.lean), [GaussianBinetBoseLiteralFrozen](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLiteralFrozen.lean)

The actual finite frozen-Pi prefixes of lengths C+r and C are compared at the same supplied time mesh and observation clock. The explicit certified mesh and clock floors give the uniform tail 11K/C.
[GaussianBinetSecondDecaySharedTail](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecaySharedTail.lean)

The actual shifted exponential antiderivative uses the rate-versus-horizon inequality directly. A common physical horizon independent of the Pi denominator now suffices to compare the actual weighted sine quadrature to each literal Binet kernel row.
[GaussianBinetFixedHorizonDecay](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetFixedHorizonDecay.lean), [GaussianBinetFixedHorizonPole](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetFixedHorizonPole.lean), [GaussianBinetFixedHorizonSine](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetFixedHorizonSine.lean), [GaussianBinetFixedHorizonFrozenRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetFixedHorizonFrozenRows.lean)

Both cutoff limits now give the original improper integral as a regular name on the encoded rational right half-plane. At independent clocks its comparison to the original compact interval [2^(-L-1),T] has leading error 2K/T + D/(4X·2^(L+1)) when D≤KX.
[GaussianBinetBoseHorizonRate](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseHorizonRate.lean), [GaussianBinetBoseImproperName](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseImproperName.lean)

The original compact product compares with the literal exponential prefix on any certified refinement. The angular precision and cutoff may be chosen before the mesh, so the same positive time tags can be used for later decay rows.
[GaussianBinetBosePrefixQuadrature](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBosePrefixQuadrature.lean), [GaussianBinetBosePrefixRefinement](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBosePrefixRefinement.lean)

The actual arctangent-weighted quadrature expands to a finite matrix and transposes with the original time weight. Each cell retains the exact signed exponential and its original time-tag-dependent observation clock.
[GaussianBinetBosePrefixTranspose](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBosePrefixTranspose.lean)

The normalized factor of two preserves the original improper name with twice the compact-cutoff error. A comparison with the first Binet integral suffices for the second identity. The positive weighted cells agree exactly with the original sine transform cells, and the zero-frequency cell has its removable value.
[GaussianBinetSecondFormulaReduction](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFormulaReduction.lean), [GaussianBinetSecondRowCell](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondRowCell.lean)

A single sine clock, horizon and grid count give error 10/2^p between the original arctangent observation and its actual damped sine rectangle for all encoded time tags bounded by the chosen horizon.
[GaussianBinetArctangentSineUniform](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetArctangentSineUniform.lean)

The literal transposed prefix compares with the frozen-Pi matrix at a separately chosen later observation clock. Each frozen column is the exact geometric row, and the zero-start matrix binds to the existing shared-mesh tail.
[GaussianBinetBoseFrozenMatrix](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenMatrix.lean), [GaussianBinetBoseFrozenOrigin](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenOrigin.lean)

The original removable column and an explicit sine quotient bound control the discarded low-frequency prefix. Every remaining frequency has an explicit positive margin, so the fixed-horizon sine transform uses a tail bound independent of raw denominator size.
[GaussianBinetFixedHorizonPositiveMargin](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetFixedHorizonPositiveMargin.lean), [GaussianBinetSineQuotientMajorant](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineQuotientMajorant.lean), [GaussianBinetSineStripCut](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineStripCut.lean), [GaussianBinetOscillatorySineSmallStrip](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetOscillatorySineSmallStrip.lean)

The literal first Binet Laplace strip and the shared-Pi finite kernel prefix use exactly the same physical tags and left weights. Their explicit cutoff bound is 14 times the physical width divided by 2^p.
[GaussianBinetKernelFrozenStrip](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrozenStrip.lean)

The original cofinal Laplace integrand has norm at most one half. Each compact left sum is bounded by half the physical width, and exact additivity gives the same leading error for the removed left interval at independent clocks.
[GaussianBinetLaplaceLowerWindow](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Strips/GaussianBinetLaplaceLowerWindow.lean)

The original frozen decay observation is moved to the exact sine evaluation clock. Replacing the original arctangent by the scheduled sine rectangle on that same grid has error T*(20+2KT)/2^q, including the original time-zero tag.
[GaussianBinetSecondWeightedSinePoint](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSinePoint.lean), [GaussianBinetSecondWeightedSineGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineGrid.lean)

The exact zero-start frozen matrix equals the original finite geometric row sum. Its scheduled sine replacement has error at most NT(20+2KT)/2^q for N rows on the same physical mesh and with the same frozen Pi sample.
[GaussianBinetSecondWeightedSinePrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSinePrefix.lean)

The weighted sine column can be evaluated at the sine rectangle clock even when the antiderivative uses a later mesh clock. The comparison to the frozen kernel row separates the dyadic clock error from the endpoint error controlled by the positive frequency margin.
[GaussianBinetSineDampedRetiming](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineDampedRetiming.lean), [GaussianBinetSineKernelCommonClock](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineKernelCommonClock.lean)

The literal frozen Pi prefix uses an explicit size-dependent tail independent of observation precision. The original positive frequency tags and integration weight read back exactly, and the literal late damping clock can be chosen independently of the Pi clock.
[GaussianBinetKernelFrozenIndependent](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrozenIndependent.lean), [GaussianBinetKernelFrequencyGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrequencyGrid.lean)

The original tags of the compact interval from 1/E to T match the corresponding suffix of the complete frozen time grid. The mesh weights agree exactly, and the time-tag comparison retains a uniform dyadic allowance.
[GaussianBinetBoseFrozenTimeRescale](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenTimeRescale.lean), [GaussianBinetBoseFrozenSuffix](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenSuffix.lean)

The original positive row majorant controls the geometric tail before the omitted zero-start time cells are restored. The combined error is 11K/I + 2KI/E², independent of the discarded geometric count.
[GaussianRationalSuffixMask](Lean/IPRADerivations/Analysis/RationalArithmetic/GaussianRationalSuffixMask.lean), [GaussianBinetSecondDecaySuffixBound](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecaySuffixBound.lean), [GaussianBinetBoseFrozenSuffixCut](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenSuffixCut.lean), [GaussianBinetBoseFrozenOriginCut](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseFrozenOriginCut.lean)

Exact finite interchange exposes each positive transposed column as the original complex damping times the original real-damped sine quadrature. The physical floor cut and low-frequency error hold on that same grid.
[GaussianBinetSecondWeightedSineMatrix](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineMatrix.lean), [GaussianBinetSecondWeightedSineTranspose](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineTranspose.lean), [GaussianBinetSecondWeightedSineSuffix](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineSuffix.lean), [GaussianBinetSecondWeightedSineCut](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineCut.lean)

Compare the literal positive sine suffix with the original first Binet improper observation via its arbitrary-mesh compact quadrature. The per-tag comparison permits different certified damping radii.
[GaussianBinetKernelFrequencyRadius](Lean/IPRADerivations/Analysis/Stirling/Binet/Kernel/GaussianBinetKernelFrequencyRadius.lean), [GaussianBinetLaplaceFrequencySuffix](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceFrequencySuffix.lean)

Checked the later frozen prefix against the weighted sine prefix on the same time grid, with an independent angular clock. The retained angular cells compare to the original frozen kernel with separately bounded observation and time-tail errors.
[GaussianBinetSecondDecayRetiming](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondDecayRetiming.lean), [GaussianBinetSineKernelFrequency](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineKernelFrequency.lean)

The compact comparison fixes the retained geometric count before choosing the literal observation clock. Refinement, freezing, suffix alignment, and the origin correction connect the original improper sample to the retained full frozen matrix with error at most 9·2^-h.
[GaussianBinetBoseLiteralLate](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLiteralLate.lean), [GaussianBinetBosePrefixRefinementLate](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBosePrefixRefinementLate.lean), [GaussianBinetBoseImproperFrozen](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseImproperFrozen.lean)

Explicit primitive-recursive schedules choose the time, geometric, and strip cutoffs, then pay independent angular, kernel, and Laplace sample budgets on one dyadic denominator.
[GaussianBinetSecondEarlySchedule](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondEarlySchedule.lean), [GaussianBinetSecondFrequencySchedule](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFrequencySchedule.lean), [GaussianBinetSecondErrorBudget](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondErrorBudget.lean)

The checked late Bose schedule admits independent lower bounds on π accuracy, the time mesh, and the final literal clock. The retained sine prefix is transposed and compared with the exact frozen kernel rectangle. Its frequency columns approximate the original first-Binet quadrature using the original mesh weight.
[GaussianBinetBoseLateSchedule](Lean/IPRADerivations/Analysis/Stirling/Binet/Bose/GaussianBinetBoseLateSchedule.lean), [GaussianBinetSecondWeightedSineTransposedPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondWeightedSineTransposedPrefix.lean), [GaussianBinetFrozenKernelRectangle](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetFrozenKernelRectangle.lean), [GaussianBinetSineKernelGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineKernelGrid.lean), [GaussianBinetSineKernelPrefix](Lean/IPRADerivations/Analysis/Stirling/Binet/Oscillatory/GaussianBinetSineKernelPrefix.lean), [GaussianBinetFrozenKernelLaplace](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetFrozenKernelLaplace.lean)

The actual first and scaled second improper observations differ by at most 35·2^-p at every common observation p. The checked first Binet identity identifies the scaled original Bose sampler with the original Stirling remainder. The object-theory theorem is universally closed.
[GaussianBinetSecondFormula](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFormula.lean)

The lifted program reads the original scaled Bose sampler at each selected rational argument. It is regular, admits an independent comparison to every sufficiently late rational observation, and is equivalent to the original named Stirling remainder on the certified right half-plane.
[GaussianNamedRightHalfPlaneLiftTransport](Lean/IPRADerivations/Analysis/Names/Rates/RightHalfPlane/GaussianNamedRightHalfPlaneLiftTransport.lean), [GaussianBinetSecondFormulaNamed](Lean/IPRADerivations/Analysis/Stirling/Binet/SecondFormula/GaussianBinetSecondFormulaNamed.lean)

The actual compact quadratures on adjacent unit intervals differ by the original logarithm quadrature with error at most 8·2^-p at the common observation clock, on every positive mesh. The upper and lower unit integrals use the same physical tags.
[GaussianRaabeUnitGridRecurrence](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeUnitGridRecurrence.lean)

A checked regular point evaluator uses the original positive-time Euler power and the reciprocal of the unscaled exponential minus one. The reciprocal has norm at most the inverse time at every observation. [The original Gamma–zeta Mellin identity](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinIdentity.lean) now identifies the corresponding improper integral on the certified rational chart.
[GaussianGammaZetaMellinIntegrand](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinIntegrand.lean)

The original real decay and cofinal Binet kernel give a positive rational floor on every bounded time interval, with an explicit observation allowance. This supplies the positive-interval estimate for the Stirling remainder moments.
[GaussianBinetLaplaceRealFloor](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceRealFloor.lean)

The literal same-clock logarithm samples give a quadratic primitive estimate on each positive rational cell. Telescoping compares the original compact logarithm quadrature to the actual endpoint difference with separate mesh and observation errors.
[GaussianRaabeLogPrimitiveCell](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeLogPrimitiveCell.lean), [GaussianRaabeLogPrimitiveGrid](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeLogPrimitiveGrid.lean)

At a rooted time t=(a/b)^A, the actual Mellin observation for the parameter s is bounded by (b/a)^(A−1)+3·2^-p on the admitted chart for s−1. The exact time factor cancels the reciprocal norm bound.
[GaussianGammaZetaMellinOriginBound](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinOriginBound.lean)

The actual compact quadrature inherits the pointwise rational floor with its physical width. On [1,2] the late samples have real part at least 1/(104·3^(2X)), with explicit dyadic admission.
[GaussianBinetLaplaceCompactRealFloor](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/GaussianBinetLaplaceCompactRealFloor.lean)

The actual unscaled reciprocal is approximated by the finite powers of the inverse of its exact positive exponential sample. On a strip with time at least 1/H the uniform error is bounded by H²/(H+N), before weighting by the original Euler power.
[GaussianGammaZetaMellinGeometric](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinGeometric.lean)

At the actual reciprocal clock, every retained geometric term compares to the original Euler decay evaluated at the positive integer multiple of time. Its inverse retiming cost has an explicit dyadic denominator.
[GaussianGammaZetaMellinDecayRows](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinDecayRows.lean)

The original logarithm observations on equal positive rational charts compare at independent precisions. Multiplication by the common physical endpoint preserves a uniform rate, including the exact grid rescaling.
[GaussianRaabeLogPrimitiveRescale](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeLogPrimitiveRescale.lean)

An exact rational t^j factor weights the original cofinal Laplace sample. On the original compact grid [1,2], every late natural moment has the same strict positive floor as the unweighted panel.
[GaussianBinetLaplaceMomentFloor](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentFloor.lean)

Each original right-tag observation is weighted by its exact powered cell width. The finite rooted grid sum is bounded by 4·2^-h as soon as its span in the root coordinate meets the certified dyadic budget.
[GaussianGammaZetaMellinOriginCell](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinOriginCell.lean), [GaussianGammaZetaMellinOriginGrid](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinOriginGrid.lean)

The deviation of the actual unit log-Gamma quadrature from the logarithm primitive has an explicit finite bound under an arbitrary integer shift. The same mesh count and observation clock are used throughout the telescope.
[GaussianRaabeUnitGridShift](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeUnitGridShift.lean)

At every actual logarithm observation on a large positive unit interval, the elementary Stirling term compares to a centered affine model with an explicit inverse-argument and dyadic error. This supplies the local estimate for the far-field average.
[GaussianRaabeStirlingCell](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeStirlingCell.lean)

An explicit modulus combines the original Laplace time estimate with the exact power t^j. It certifies regularity of the original weighted quadrature on arbitrary admissible compact strips and on [1,2].
[GaussianBinetLaplaceMomentCompact](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentCompact.lean)

The centered left grid has exact mean −1/(2N). Averaging the checked elementary Stirling samples gives the literal endpoint primitive with the explicit inverse-argument error, dyadic error, and a mesh-bias coefficient independent of the mesh.
[GaussianRaabeCenteredMesh](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeCenteredMesh.lean), [GaussianRaabeAffineMean](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeAffineMean.lean), [GaussianRaabeStirlingMesh](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeStirlingMesh.lean)

The exact rational weight commutes with the original horizon comparison. Weighted compact integrals agree whenever both charts cover the same physical panel, including the independently sampled row comparison.
[GaussianBinetLaplaceMomentHorizon](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentHorizon.lean)

At a common admissible horizon, the original weighted quadrature on consecutive strips agrees with the sum of their regular names.
[GaussianBinetLaplaceMomentAdditivity](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentAdditivity.lean)

The original positive-window Mellin observations compare with the finite weighted Euler decay prefix on the same physical tags. A computed common clock controls the decay rows and leaves the exact geometric truncation allowance.
[GaussianGammaZetaMellinDecayPrefix](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinDecayPrefix.lean), [GaussianGammaZetaMellinStrip](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinStrip.lean)

The original real Stirling remainder controls actual common-clock log-Gamma and logarithm observations. Explicit schedules bound the finite shift, elementary and remainder errors after choosing the distant interval and mesh. The right side is the regular name for the logarithm primitive plus the original Stirling constant.
[GaussianRaabeStirlingRemainder](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeStirlingRemainder.lean), [GaussianRaabeRightSide](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeRightSide.lean), [GaussianRaabeCofinalSchedule](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeCofinalSchedule.lean)

The original weighted finite Mellin rectangle can be summed first over time or first over the decay index. The transposed columns retain the actual Euler samples at positive integer multiples of the original time tags.
[GaussianGammaZetaMellinTranspose](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinTranspose.lean)

The original weighted compact observations have a physical width bound. In the unit time window the bound is the width itself, uniformly in the internal natural moment order.
[GaussianBinetLaplaceMomentWidth](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentWidth.lean)

The original reciprocal exponential and exact weight yield an inverse-square bound with the explicit factorial coefficient and uniform dyadic allowance.
[GaussianBinetLaplaceMomentDecay](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentDecay.lean)

The common affine-grid inverse-square estimate bounds the original weighted quadrature uniformly in the total width and the chosen covering horizon.
[GaussianBinetLaplaceMomentTail](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentTail.lean)

At any mesh above the computed floor, the actual log-Gamma quadrature and the regular right side differ by at most 14·2^-h at the selected clock. The mesh may be aligned to a separate endpoint partition. The exact encoded unit argument has an explicit comparison to the original Stirling constant minus one.
[GaussianRaabeStirlingGridRemainder](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeStirlingGridRemainder.lean), [GaussianRaabePositiveComparison](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabePositiveComparison.lean), [GaussianRaabeAtOne](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeAtOne.lean)

The exact moment names on ordered positive windows have the original inverse-square tail rate at independent precisions.
[GaussianBinetLaplaceMomentPrefixes](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentPrefixes.lean)

An explicit cofinal cutoff gives a regular name of the weighted original Laplace integrand. Its independent comparison to every original compact prefix retains the inverse-horizon tail bound.
[GaussianBinetLaplaceMomentImproper](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentImproper.lean)

The actual weighted rows have nonnegative real limits, and the common quadrature preserves the real order.
[GaussianBinetLaplaceMomentNonnegative](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNonnegative.lean)

The original weighted Mellin strip compares to a finite sum of the actual positive-scaling damped Euler quadratures for the scales 1 through N, with a scheduled geometric and dyadic error.
[GaussianGammaZetaMellinDampedPoint](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedPoint.lean), [GaussianGammaZetaMellinDampedStrip](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedStrip.lean)

The arbitrary-width recurrence binds the original positive-strip observations exactly. Equal rational tags give aligned grids for the full and trimmed unit panels. A uniform unit-panel bound controls the omitted strip, and the original logarithm primitive has an explicit bound at the dyadic endpoint.
[GaussianRaabeStripGridRecurrence](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeStripGridRecurrence.lean), [GaussianRaabeLogGammaAlignedTime](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeLogGammaAlignedTime.lean), [GaussianRaabeUnitStripBound](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeUnitStripBound.lean), [GaussianRaabeOriginStripAlignment](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeOriginStripAlignment.lean), [GaussianRaabeDyadicPrimitive](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeDyadicPrimitive.lean)

On the aligned trimmed grid, the actual logarithm quadrature approximates minus one with separate mesh, observation, and dyadic-endpoint errors.
[GaussianRaabeOriginLogStrip](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeOriginLogStrip.lean)

Certifies a common finite cutoff, aligned meshes and observation clock, with separate bounds for both omitted endpoint contributions and the original truncated logarithm quadrature.
[GaussianRaabeOriginSchedule](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeOriginSchedule.lean)

Every moment on the positive real chart has a named positive lower bound, witnessed by the compact unit panel and the nonnegative exterior strips of each cofinal prefix.
[GaussianBinetLaplaceMomentPositive](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentPositive.lean)

The actual left sums on [x,x+1] give a regular name at every encoded positive rational x and are independently-precision cross-equivalent to x log x − x plus the original Stirling constant. The comparison is universally closed in iPRA.
[GaussianRaabeFormula](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeFormula.lean)

An internally finite sum of positively scaled improper Euler values is independently-precision equivalent to the original Gamma name times the corresponding finite Dirichlet sum. This proves the finite factorization on the original scaled evaluators before the infinite limit.
[GaussianNamedFiniteSumFamilyMultiply](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilyMultiply.lean), [GaussianGammaZetaMellinDampedImproper](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedImproper.lean)

The original quadratures on [2⁻ʰ,1] satisfy the certified 39/2^k comparison with the actual half-log(2π) observation. The padded cofinal schedule gives a regular improper name cross-equivalent to the named constant by a closed iPRA proof.
[GaussianRaabeOriginComparison](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeOriginComparison.lean), [GaussianRaabeUnitIntegral](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeUnitIntegral.lean)

The original [1,2] quadratures at each exact shifted unit-grid tag give a regular name for the integral of logΓ(1+t) on [0,1]. It is cross-equivalent to the named Stirling constant minus the exact rational unit.
[GaussianRaabeShiftedUnitFormula](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeShiftedUnitFormula.lean)

Every nonnegative rational argument s admits an original observation bound 3s²+2/2^p against 1−s. This bound will control the Taylor remainder in the weighted Binet integral.
[GaussianEulerDecayGlobalTaylor](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayGlobalTaylor.lean)

The actual weighted and unweighted quadratures agree in the zeroth order on every shared physical panel. The checked cofinal rates then identify the two original improper names.
[GaussianBinetLaplaceMomentZeroOrder](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentZeroOrder.lean)

The original real Stirling remainder is cross-equivalent to the actual improper Binet moment at order zero and its canonical radius, by a universally closed iPRA proof.
[GaussianBinetLaplaceMomentStirling](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentStirling.lean)

Each original finite damped panel on a rational grid compares to its actual improper Euler row with a certified scaled endpoint allowance and a common mesh and observation clock.
[GaussianGammaZetaMellinDampedExhaustion](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedExhaustion.lean)

The named expression x log x − x plus the original Stirling constant admits a uniform rate to its rational counterpart at every actual late input observation. The coefficient is independent of the frozen numerator and denominator.
[GaussianRaabeNamedRightSide](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeNamedRightSide.lean)

Every sufficiently late actual rational observation of the input and every sufficiently fine original log-Gamma grid at that base satisfy an independent-precision comparison with the named Raabe expression. The selected primitive-recursive schedule gives a regular name and a universally closed equivalence for each input sampler.
[GaussianRaabeNamedGrid](Lean/IPRADerivations/Analysis/Stirling/Raabe/GaussianRaabeNamedGrid.lean)

A certified enclosing panel, shared mesh and observation clock give an explicit independent-precision rate from the literal finite damped quadrature sum to Gamma times the original finite Dirichlet sum.
[GaussianGammaZetaMellinDampedWindow](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedWindow.lean)

For every internal finite prefix, the explicit widened physical panel contains the given positive panel. The chosen bounds and mesh make its literal damped sum agree with the original finite Gamma–Dirichlet product within 10/2^p+1/2^r at independent precisions.
[GaussianGammaZetaMellinDampedWindowSchedule](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinDampedWindowSchedule.lean)

The same-clock original Mellin observation factors the finite geometric prefix. Its uniform factor two gives a prefix-count independent norm bound at each positive time and on the powered lower endpoint cells.
[GaussianGammaZetaMellinGeometricEnvelope](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinGeometricEnvelope.lean)

The original Mellin evaluator agrees exactly with the finite-strip grid. Its sampled denominator retains a positive factorial monomial after subtracting one, giving an inverse-square observation bound. The checked scalar telescoper bounds any shared-step upper panel independently of its right endpoint.
[GaussianGammaZetaMellinGrid](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinGrid.lean), [GaussianGammaZetaMellinUpperPoint](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinUpperPoint.lean), [GaussianGammaZetaMellinUpperGrid](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinUpperGrid.lean)

At a common observation clock, the actual weighted moments have the next time power as the exact linear coefficient. The quadratic majorant is the nonnegative frozen moment two orders higher, plus a uniform dyadic observation allowance.
[GaussianEulerDecayGlobalIncrement](Lean/IPRADerivations/Analysis/Euler/Integration/Decay/GaussianEulerDecayGlobalIncrement.lean), [GaussianBinetLaplaceMomentFrozenRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentFrozenRows.lean), [GaussianBinetLaplaceMomentTaylorRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentTaylorRows.lean)

The original quadratures on a shared physical grid satisfy the right Taylor comparison. The leading norm allowance is three times the squared increment times a norm bound for the original moment two orders higher. The remaining dyadic cost is proportional to physical width and independent of mesh size.
[GaussianBinetLaplaceMomentTaylorMajorant](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentTaylorMajorant.lean), [GaussianBinetLaplaceMomentTaylorGrid](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentTaylorGrid.lean)

Every certified positive rational panel has an explicit sampled modulus at independent time encodings and observation clocks. The actual ordinary affine quadrature is a regular name, proved in iPRA.
[GaussianGammaZetaMellinReciprocalRate](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinReciprocalRate.lean), [GaussianGammaZetaMellinCompact](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinCompact.lean)

The actual compact name on nested powered positive cutoffs obeys an origin bound independent of the inner endpoint. The proof groups the original affine quadrature into powered cells and controls the drift to each right tag.
[GaussianEulerLowerTailRootedMajorant](Lean/IPRADerivations/Analysis/Euler/PositiveAxis/LowerBounds/GaussianEulerLowerTailRootedMajorant.lean), [GaussianGammaZetaMellinLowerRooted](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinLowerRooted.lean)

The actual inverse-power row equals the reciprocal-time original power times its exact rational scale. A certified real-part margin gives a dyadic block decay bound at arbitrary original observation clocks.
[GaussianGammaZetaDirichletReciprocalRow](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletReciprocalRow.lean), [GaussianGammaZetaDirichletPowerOrder](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletPowerOrder.lean), [GaussianGammaZetaDirichletRowDecay](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletRowDecay.lean)

The actual same-clock shifted improper observation compares to the original base minus the exact increment times the successor moment. The quadratic allowance uses a uniform norm bound on the actual higher moment and the remaining term is 10/2^p.
[GaussianBinetLaplaceMomentImproperBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentImproperBound.lean), [GaussianBinetLaplaceMomentImproperTaylor](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentImproperTaylor.lean)

The original Dirichlet sums converge at the certified margin with the explicit dyadic-block rate for every sufficiently long finite prefix. The original normalized Gamma product has the corresponding independent-observation rate.
[GaussianGammaZetaDirichletBlock](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletBlock.lean), [GaussianGammaZetaDirichletTail](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletTail.lean), [GaussianGammaZetaDirichletFiniteRate](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletFiniteRate.lean), [GaussianGammaZetaDirichletCofinal](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletCofinal.lean), [GaussianGammaZetaDirichletProduct](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletProduct.lean)

At each encoded positive rational base, the original punctured forward difference quotient converges to the negative of the next moment with explicit linear step error and independent dyadic observation errors.
[GaussianBinetLaplaceMomentForwardQuotient](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentForwardQuotient.lean)

Exact rescaling and two compact endpoint bounds give a uniform comparison through enclosing powered windows. The cofinal sampler of the original affine log-power and reciprocal integrand is a regular name by a universally closed iPRA judgment.
[GaussianGammaZetaMellinCompactUpperTail](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinCompactUpperTail.lean), [GaussianGammaZetaMellinCutoffWindows](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinCutoffWindows.lean), [GaussianGammaZetaMellinNestedBound](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinNestedBound.lean), [GaussianGammaZetaMellinImproper](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinImproper.lean)

Exact transposition binds the finite evaluator to the original damped grid. Uniform lower and upper estimates are independent of the finite count. A powered enclosing window compares the actual compact finite sum with the original Gamma–Dirichlet product at independent observation clocks.
[GaussianGammaZetaMellinFiniteDampedEvaluator](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedEvaluator.lean), [GaussianGammaZetaMellinFiniteDampedModulus](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedModulus.lean), [GaussianGammaZetaMellinFiniteDampedGrid](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedGrid.lean), [GaussianGammaZetaMellinFiniteDampedLower](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedLower.lean), [GaussianGammaZetaMellinFiniteDampedUpper](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedUpper.lean), [GaussianGammaZetaMellinPoweredWindow](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinPoweredWindow.lean), [GaussianGammaZetaMellinPoweredCompactProduct](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinPoweredCompactProduct.lean)

The original compact Mellin pullback and the actual finite Euler damped compact sampler agree up to the checked uniform error on a fixed positive panel, with a concrete lower threshold on the count.
[GaussianGammaZetaMellinFiniteDampedComparison](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteDampedComparison.lean)

A primitive-recursive envelope depending on the order and the positive rational margin bounds all observations of the original improper moment uniformly in the base chart denominator.
[GaussianBinetLaplaceMomentMarginRows](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentMarginRows.lean), [GaussianBinetLaplaceMomentMarginTail](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentMarginTail.lean), [GaussianBinetLaplaceMomentMarginBound](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentMarginBound.lean)

A fixed positive core panel, count-independent exterior estimates and original finite Euler scaling identify the actual Mellin improper sampler with Gamma times the original cofinal Dirichlet series, by a closed iPRA derivation at independently chosen observation precisions.
[GaussianGammaZetaMellinFiniteNested](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteNested.lean), [GaussianGammaZetaMellinFiniteNestedBound](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteNestedBound.lean), [GaussianGammaZetaMellinFiniteCompactUpper](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/EndpointBounds/GaussianGammaZetaMellinFiniteCompactUpper.lean), [GaussianGammaZetaMellinFiniteWindowTail](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Damped/GaussianGammaZetaMellinFiniteWindowTail.lean), [GaussianGammaZetaMellinIdentity](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinIdentity.lean)

The fixed-presentation convexity law gives the paper’s chord for every natural block size, including the right endpoint. The literal named bracket difference is x times the logarithm of the endpoint ratio. Its checked bounds give both the exact rational width bound and the stated dyadic cutoff.
[GaussianBohrMollerupBlockChord](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBlockChord.lean), [GaussianBohrMollerupBracketEndpoints](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketEndpoints.lean), [GaussianBohrMollerupBracketWidth](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketWidth.lean)

Any two positive rational input charts with the same quotient give equivalent observations of the original improper Binet moment. The closed theorem compares independently chosen observation precisions and allows separate certified chart radii.
[GaussianBinetLaplaceMomentRescale](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentRescale.lean)

Iterating the exact fixed-presentation recurrence gives the actual shifted logarithm sum at every finite block length. Each term is bounded by the last logarithm, giving the closed finite-sum comparison for the larger block chord.
[GaussianBohrMollerupFiniteRecurrence](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupFiniteRecurrence.lean), [GaussianBohrMollerupBlockLogBound](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBlockLogBound.lean)

For every internal moment order, the original forward and backward difference quotients converge to the negative successor moment at the same fixed rational base. The theorem gives explicit error budgets and independent observation clocks for positive rational steps bounded by 1/(2D) at a base X/D.
[GaussianBinetLaplaceMomentBackwardWindow](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentBackwardWindow.lean), [GaussianBinetLaplaceMomentBackwardQuotient](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentBackwardQuotient.lean)

At the concrete argument two, the original exponential Dirichlet row equals the literal rational reciprocal square. The proof doubles the original logarithm and identifies its exponential with the product of the two original reciprocal-base exponentials.
[GaussianGammaZetaDirichletSquareRow](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/Square/GaussianGammaZetaDirichletSquareRow.lean)

The integer factorial normalization and exact finite log recurrence transport the two convexity chords to the original finite lower and upper bracket names. A closed iPRA derivation places the fixed presentation between those names for every encoded positive rational x at most B and every n at least two.
[GaussianBohrMollerupFactorialNormalization](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupFactorialNormalization.lean), [GaussianBohrMollerupBracketIncrements](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketIncrements.lean), [GaussianBohrMollerupBracketEnclosure](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/FiniteBrackets/GaussianBohrMollerupBracketEnclosure.lean)

The checked integer Gamma trajectory and actual factorial readback give Gamma(2)=1 on the native Mellin chart. The closed specialization equates the original improper sampler with its original cofinal Dirichlet name at two.
[GaussianGammaZetaMellinTwoDirichlet](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinTwoDirichlet.lean)

Using the same paper cutoff for both presentations gives an independent-clock comparison through their original bracket names. Removing the dyadic error identifies the two presentations and gives the corresponding original positive Gamma uniqueness statement.
[GaussianBohrMollerupLiteralUniqueness](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/GaussianBohrMollerupLiteralUniqueness.lean)

At every common finite cutoff the actual exponential rows give the literal finite reciprocal-square sum. The two checked tail rates then identify the original cofinal Dirichlet name with the original rational reciprocal-power name and transfer the Basel evaluation.
[GaussianGammaZetaDirichletSquareFinite](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/Square/GaussianGammaZetaDirichletSquareFinite.lean), [GaussianGammaZetaDirichletSquareCofinal](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/Square/GaussianGammaZetaDirichletSquareCofinal.lean)

The specialized Mellin integrand is the rational time multiplied by the original reciprocal of the unscaled exponential minus one at all positive rational points. The original improper name equals pi squared divided by six by closed iPRA name equality.
[GaussianGammaZetaMellinTwoIntegrand](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinTwoIntegrand.lean), [GaussianGammaZetaMellinBasel](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/GaussianGammaZetaMellinBasel.lean)

The original moment varies linearly with the step on a common certified positive margin. The signed chart version transports this bound through exact rational coordinates and covers either order of the endpoints at independent observation clocks.
[GaussianBinetLaplaceMomentVariation](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentVariation.lean), [GaussianBinetLaplaceMomentSignedVariation](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentSignedVariation.lean)

The primitive-recursive evaluator takes the actual late signed samples of a regular input with a certified positive real-part margin. The named moment is regular and proper for every internal order, and the comparison with each sufficiently late original rational evaluation has an independent observation rate.
[GaussianBinetLaplaceMomentNamed](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamed.lean)

On canonical real input observations with a certified positive margin, the original named Stirling remainder agrees with the named zeroth Binet moment. The comparison retains the original observation clocks on both names.
[GaussianBinetLaplaceMomentNamedStirling](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedStirling.lean)

The compiled fixed presentation evaluates its actual rational program on the incoming real name’s late samples. The literal rational squeeze and native continuity give a regular real lift, identify the original named log-Gamma, and recover the original named Gamma by exponentiating that lift.
[GaussianBohrMollerupNamedFrozen](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/Named/GaussianBohrMollerupNamedFrozen.lean), [GaussianBohrMollerupNamedLift](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/Named/GaussianBohrMollerupNamedLift.lean), [GaussianBohrMollerupNamedGamma](Lean/IPRADerivations/Analysis/Gamma/BohrMollerup/Named/GaussianBohrMollerupNamedGamma.lean)

The literal finite summation program propagates a bounded family of row comparisons at independently chosen observation clocks. Only the spatial error grows with the internal summation length.
[GaussianNamedFiniteSumFamilyRate](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteSumFamilyRate.lean)

On a fixed compact time panel the actual Euler log-power has a checked parameter rate. The same estimate controls each original Mellin integrand sample and the original Dirichlet row. A common, internally chosen truncation and the existing Dirichlet tail rates give a primitive-recursive input demand for every independent cofinal observation error.
[GaussianEulerCompactPowerParameterRate](Lean/IPRADerivations/Analysis/Euler/CompactExhaustion/GaussianEulerCompactPowerParameterRate.lean), [GaussianGammaZetaParameterRates](Lean/IPRADerivations/Analysis/Gamma/Zeta/GaussianGammaZetaParameterRates.lean), [GaussianGammaZetaDirichletParameterRate](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletParameterRate.lean)

A primitive-recursive maximum of the input demands selects actual late signed samples. The checked lift is regular and proper, agrees with arbitrary later frozen rational evaluations, and preserves rational agreement for two evaluators using the same demand.
[GaussianNamedRightHalfPlaneDemandLift](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlaneDemandLift.lean), [GaussianNamedRightHalfPlaneDemandComparison](Lean/IPRADerivations/Analysis/Names/RightHalfPlane/GaussianNamedRightHalfPlaneDemandComparison.lean)

The literal [1,2] panel supplies the explicit lower bound 2/(104·3^(2S)) at every internal order under the certified real upper radius S. The named proof gives strict order and a computed original sample with at least half that lower bound.
[GaussianBinetLaplaceMomentNamedPositive](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedPositive.lean)

Both actual difference quotients converge to the negative successor moment on a common fixed positive margin. The leading constants depend on the internal order and the physical margin and work for every denominator encoding of the base.
[GaussianBinetLaplaceMomentForwardMargin](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentForwardMargin.lean), [GaussianBinetLaplaceMomentTwoSidedMargin](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentTwoSidedMargin.lean)

Uniform Gamma and Dirichlet sample bounds and the independent factor rates yield a concrete primitive-recursive input demand for the original normalized product on the certified rational half-plane.
[GaussianGammaZetaDirichletUniformBound](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletUniformBound.lean), [GaussianGammaZetaDirichletProductParameterRate](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletProductParameterRate.lean)

The signed native numerator, denominator, and certified wider radius give a common rational chart. The three actual rational providers share one input demand for Gamma, the cofinal Dirichlet series, and their original normalized product.
[GaussianGammaZetaNamedChart](Lean/IPRADerivations/Analysis/Gamma/Zeta/GaussianGammaZetaNamedChart.lean)

For a regular name with real part bounded below by one plus an explicit margin, the original subtraction sampler supplies the certified s−1 chart. Shifting back identifies the original input at independent clocks.
[GaussianGammaZetaNamedInput](Lean/IPRADerivations/Analysis/Gamma/Zeta/GaussianGammaZetaNamedInput.lean)

The original normalized quotient has the exact paper logarithmic and relative bounds 4A(A+1)/x and 8A(A+1)/x on a common rational chart, including noninteger A, reversed or equal endpoints, and the stated relative-error threshold.
[GaussianGammaDigammaTwoShiftExactFiniteRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftExactFiniteRate.lean), [GaussianGammaDigammaTwoShiftRationalWindow](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftRationalWindow.lean), [GaussianGammaDigammaTwoShiftExactCofinalRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftExactCofinalRate.lean), [GaussianGammaDigammaTwoShiftRationalRate](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftRationalRate.lean)

At a certified positive real name, both actual normalized difference quotients agree in the limit with the negative successor moment from the same unshifted input. Their independent observation bounds have explicit leading rate proportional to the step size on the fixed physical margin.
[GaussianNamedDifferenceQuotientRate](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNamedDifferenceQuotientRate.lean), [GaussianBinetLaplaceMomentNamedShift](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedShift.lean), [GaussianBinetLaplaceMomentNamedDerivative](Lean/IPRADerivations/Analysis/Stirling/Binet/Laplace/Moments/GaussianBinetLaplaceMomentNamedDerivative.lean)

A shared late signed input sample compares the Gamma chart provider with the repository’s original named Gamma on the actual input. The adapter admits the original argument directly and proves agreement at independent output clocks.
[GaussianGammaZetaNamedGammaAlignment](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedGammaAlignment.lean)

Both original samplers are evaluated on actual late signed samples with the same certified input demand. Closed iPRA name equality extends their rational identity to every regular input name on the certified half-plane.
[GaussianGammaZetaMellinParameterRate](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Compact/GaussianGammaZetaMellinParameterRate.lean), [GaussianGammaZetaNamedHalfPlane](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedHalfPlane.lean)

An explicit shared late clock encodes three original positive real names on one rational denominator. The three original logarithm evaluators have independent observation rates against their actual common-chart values.
[GaussianGammaDigammaTwoShiftNamedFreeze](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedFreeze.lean)

A common actual late signed sample compares the original normalized product with the product of separately regular factors. The Gamma factor is the original named Gamma evaluated directly at s. The closed iPRA formula holds under an explicit positive margin for Re(s) above one.
[GaussianGammaZetaNamedFactors](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedFactors.lean), [GaussianGammaZetaNamedMellin](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedMellin.lean)

The original finite and cofinal Dirichlet sums agree across equal rational encodings and independently certified charts. The original named Dirichlet and Mellin values are proper for equivalent input names with independently chosen margin certificates.
[GaussianGammaZetaDirichletOverlap](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletOverlap.lean), [GaussianGammaZetaDirichletPresentation](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaDirichletPresentation.lean), [GaussianGammaZetaNamedDirichletOverlap](Lean/IPRADerivations/Analysis/Gamma/Zeta/Dirichlet/GaussianGammaZetaNamedDirichletOverlap.lean), [GaussianGammaZetaNamedMellinOverlap](Lean/IPRADerivations/Analysis/Gamma/Zeta/Mellin/Named/GaussianGammaZetaNamedMellinOverlap.lean)

The checked shifts repair sample windows that meet the named boundary, including the relative-error threshold. A cofinal named order comparison removes errors that can be made arbitrarily small while retaining independent observation precisions.
[GaussianNamedCofinalOrder](Lean/IPRADerivations/Analysis/Names/Order/GaussianNamedCofinalOrder.lean), [GaussianGammaDigammaTwoShiftWindowBuffer](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftWindowBuffer.lean)

The actual cubic Mercator rows have the explicit rational Gaussian bound and rounded-observation rate. Summing the original finite rows gives the paper’s tail radius and the corrected Barnes cutoff.
[GaussianBarnesCanonicalLogRow](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogRow.lean), [GaussianBarnesCanonicalLogTail](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogTail.lean), [GaussianBarnesCanonicalLogObservation](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogObservation.lean)

The original named logarithmic quotient and its normalized exponential are regular and have explicit independent-clock rates against their actual common-chart rational equivalents. This supplies the cofinal comparison needed for exact named window bounds.
[GaussianGammaDigammaTwoShiftNamedBinding](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedBinding.lean), [GaussianGammaDigammaTwoShiftNamedExponential](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedExponential.lean)

The signed exponent is unchanged by translating the base and both shifted arguments on a common denominator. The original logarithmic quotient has a linear independent observation rate for this translation on the certified local positive window.
[GaussianGammaDigammaTwoShiftLogGammaTranslation](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftLogGammaTranslation.lean), [GaussianGammaDigammaTwoShiftQuotientTranslation](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Rational/GaussianGammaDigammaTwoShiftQuotientTranslation.lean)

The actual rounded cubic rows split at a fixed head boundary. The corrected Barnes endpoint and a proved row precision budget give a regular primitive-recursive Gaussian name on each rational disk, including the empty tail at radius zero.
[GaussianBarnesCanonicalLogRoundedTail](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogRoundedTail.lean), [GaussianBarnesCanonicalLogSchedule](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogSchedule.lean), [GaussianBarnesCanonicalLogCofinal](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogCofinal.lean)

The two original exponential factors use the named Stirling constant and Euler–Mascheroni constant. Their literal product is regular and agrees at independent clocks with the exponential of the combined exponent.
[GaussianBarnesCanonicalPrefactor](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactor.lean)

The head evaluates each literal polynomial power times its original exponential, with a uniform disk cap. Arbitrary consecutive finite products are regular and split exactly, including possible zero factors. The original prefactor has a checked inverse and apartness certificate.
[GaussianBarnesCanonicalPrefactorInverse](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorInverse.lean), [GaussianBarnesCanonicalFactor](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalFactor.lean), [GaussianBarnesCanonicalHead](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHead.lean), [GaussianBarnesCanonicalHeadSplit](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadSplit.lean)

The actual fixed interval and regular cofinal logarithm satisfy the exact independent-clock leading error $2R^3/(3N)$. The bounded exponential and fixed prefactor and head propagate that rate to the actual split Barnes sampler.
[GaussianBarnesCanonicalFiniteLog](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalFiniteLog.lean), [GaussianBarnesCanonicalLogIntervalRate](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogIntervalRate.lean), [GaussianBarnesCanonicalLogCofinalRate](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogCofinalRate.lean), [GaussianBarnesCanonicalTailExponential](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTailExponential.lean), [GaussianBarnesCanonicalValue](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalValue.lean)

The actual cubic logarithm agrees with the original local logarithm after cancellation of its first two terms. On the tail disk this gives an exact independent-clock identification of each exponentiated row with the literal direct Barnes factor.
[GaussianBarnesCanonicalCubicName](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalCubicName.lean), [GaussianBarnesCanonicalCorrection](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalCorrection.lean), [GaussianBarnesCanonicalLogFactor](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogFactor.lean)

An exact Gaussian integer numerator test identifies the original factor base zeros at the corresponding negative integers and supplies a rational lower bound on each nonzero base.
[GaussianBarnesCanonicalBase](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalBase.lean)

The ordinary named real-order hypotheses control a common late dyadic chart. The original named cap $4A(A+1)/x$ and its size guard have independent rates to the actual finite rational chart values.
[GaussianNamedFrozenScalarOrder](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedFrozenScalarOrder.lean), [GaussianGammaDigammaTwoShiftNamedWindow](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedWindow.lean), [GaussianGammaDigammaTwoShiftNamedChart](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedChart.lean), [GaussianGammaDigammaTwoShiftNamedSize](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedSize.lean), [GaussianGammaDigammaTwoShiftNamedCap](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedCap.lean)

The original normalized quotient on regular real names with a certified positive margin obeys the exact logarithmic bracket with radius $4A(A+1)/x$ and the exact relative bracket with radius $8A(A+1)/x$. The latter assumes $4A(A+1)\le x$. The repaired charts include equality at the window boundaries.
[GaussianGammaDigammaTwoShiftCapRepair](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftCapRepair.lean), [GaussianGammaDigammaTwoShiftChartProper](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftChartProper.lean), [GaussianGammaDigammaTwoShiftNamedRepairedChart](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedRepairedChart.lean), [GaussianGammaDigammaTwoShiftNamedLogOrder](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedLogOrder.lean), [GaussianGammaDigammaTwoShiftNamedRelativeOrder](Lean/IPRADerivations/Analysis/Gamma/Digamma/TwoShift/Named/GaussianGammaDigammaTwoShiftNamedRelativeOrder.lean)

A nonzero rational base gives an explicit lower bound on the original positive power times the actual exponential at every sufficiently late sample.
[GaussianBarnesCanonicalFactorApartness](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalFactorApartness.lean)

The actual finite cubic logarithmic sum exponentiates to the actual literal finite factor product. The internal finite fold includes the empty interval.
[GaussianNamedFiniteExponentialFold](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedFiniteExponentialFold.lean), [GaussianBarnesCanonicalFiniteLogRows](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalFiniteLogRows.lean), [GaussianBarnesCanonicalFiniteLogProduct](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalFiniteLogProduct.lean)

At any common cutoff, independent certified disk radii give the same represented finite product. The comparison passes through the original row and prefactor samplers and permits zero factors.
[GaussianBarnesCanonicalFiniteRadius](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalFiniteRadius.lean)

The original finite prefactor and factors at each admitted cutoff compare at independent clocks with the regular canonical Barnes sampler. A verified primitive-recursive cutoff at each admitted rational input gives leading error at most $2^{-p}$ for every later truncation.
[GaussianBarnesCanonicalProduct](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalProduct.lean)

The same encoded Gaussian rational in two positive-denominator presentations gives equivalent names for the original factor, prefactor and full finite product on independently certified disks.
[GaussianBarnesCanonicalFiniteProperness](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalFiniteProperness.lean)

At zero input every sample of the literal finite canonical product is exactly one. The original cofinal sampler represents one for every admitted radius and positive denominator, proving $G(1)=1$.
[GaussianBarnesCanonicalNormalization](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalNormalization.lean)

A bounded search across actual factor bases identifies an exact zero in the finite product or builds a quantitative late observation certificate of apartness.
[GaussianBarnesCanonicalHeadApartness](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadApartness.lean)

Two original regular names with explicit apartness witnesses give apartness at the actual retimed product observation.
[GaussianNamedProductApartness](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedProductApartness.lean)

The exact exponential of the negated cofinal logarithm supplies a named inverse and quantitative apartness of the actual tail sampler.
[GaussianBarnesCanonicalTailApartness](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTailApartness.lean)

For the original sampler $F(z)=G(1+z)$ on admitted Gaussian rational inputs, a bounded witness search gives exact pointwise zero exactly at the negative integers, and gives apartness at all other inputs. The ordinary Cauchy-name zero envelope implies the same witness. Analytic multiplicities remain open.
[GaussianBarnesCanonicalValueZeros](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalValueZeros.lean)

An explicit bound on the actual prefactor and fixed head gives a single primitive-recursive cutoff depending only on the disk radius and requested precision. Every admitted rational input and every later literal product obey the same leading dyadic error.
[GaussianBarnesCanonicalDiskBound](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalDiskBound.lean), [GaussianBarnesCanonicalUniformCutoff](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalUniformCutoff.lean)

The original cofinal sampler represents the same value under different disk radii and denominator encodings of the same Gaussian rational. Both comparisons use a common literal cutoff and eliminate the leading dyadic errors by a finite rational gap query.
[GaussianBarnesCanonicalProperness](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalProperness.lean)

Explicit disk and index bounds give an independent-clock Lipschitz rate for the actual factor observations, including separately encoded Gaussian rational inputs.
[GaussianBarnesCanonicalFactorLipschitz](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalFactorLipschitz.lean)

The original finite product at each common segment has an explicit independent-clock Lipschitz bound. The proof retains different rational encodings and each product normalization, including empty segments.
[GaussianBarnesCanonicalHeadLipschitz](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadLipschitz.lean)

The actual rational first-derivative expression has radius $2R^2/k^2$ and its exact finite tail has radius $2R^2/N$. The cofinal derivative quotient proof uses this bound to keep the rational slope error uniform in the truncation.
[GaussianBarnesCanonicalDerivativeRow](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeRow.lean), [GaussianReciprocalSquareInterval](Lean/IPRADerivations/Analysis/Series/ReciprocalSquares/GaussianReciprocalSquareInterval.lean), [GaussianBarnesCanonicalDerivativeTail](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeTail.lean)

The original factor equals the exact rational power $(z+m)^m$ times its actual regular exponential multiplier, with a certified positive lower bound.
[GaussianBarnesCanonicalDeflatedFactor](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedFactor.lean)

The original ranges on both sides of the isolated index are apart throughout the certified closed half-unit rational neighborhood. The disk guard forces the chosen factor into the fixed initial head.
[GaussianBarnesCanonicalDeflatedHead](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedHead.lean)

On each common rational disk, an explicit input clock certifies a dyadic value budget for the original cofinal evaluator. The estimate combines the literal prefactor and head variation with two uniform convergence errors.
[GaussianBarnesCanonicalPrefactorLipschitz](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorLipschitz.lean), [GaussianBarnesCanonicalUniformContinuity](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalUniformContinuity.lean)

On each admitted half-unit neighborhood of a negative integer, the actual Barnes value equals the exact power of the shifted input times a regular coefficient with explicit apartness. The original prefactor, remaining finite ranges and cofinal tail supply that coefficient. The analytic multiplicity theorem still requires the analytic contracts.
[GaussianBarnesCanonicalDeflatedValue](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedValue.lean)

The exact sums of the literal first-derivative rows give a regular sampler with an explicit cofinal length and tail modulus. The original tail logarithm’s divided differences converge to this sampler at the rate given in the cofinal logarithm derivative entry.
[GaussianBarnesCanonicalDerivativeCofinal](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeCofinal.lean)

The original rational evaluator, applied to an explicit late original input observation, gives a regular Barnes name. On a common certified disk it respects equivalent input names and agrees with the original rational value on constant inputs. The disk can be computed from the input name.
[GaussianBarnesCanonicalNamedDemand](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedDemand.lean), [GaussianBarnesCanonicalNamed](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamed.lean)

Throughout the certified half-unit neighborhood, each retained factor has a lower bound independent of the input numerator and denominator. The same uniform apartness holds at the exact skipped-head observation.
[GaussianBarnesCanonicalDeflatedHeadUniform](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedHeadUniform.lean)

The three admitted Mercator names satisfy the exact addition and difference identity when their rational bases multiply. This supplies an exact name identity for the Barnes derivative comparison.
[GaussianLocalLogarithmMultiplicativeIncrement](Lean/IPRADerivations/Analysis/Logarithm/Local/GaussianLocalLogarithmMultiplicativeIncrement.lean)

The original factor at the conjugate rational input is the conjugate of the original factor at the input. The proof covers all admissible positive indices and permits a zero factor.
[GaussianBarnesCanonicalFactorConjugation](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalFactorConjugation.lean)

The exact original named Barnes outputs agree for equivalent input names with separately certified radii. The proof compares a common pair of actual late rational inputs and eliminates independent dyadic error terms.
[GaussianBarnesCanonicalNamedFrozen](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFrozen.lean)

The genuine exponential factors at their actual multiplication clock satisfy a rational lower bound depending only on the disk radius. This gives uniform apartness at a computed observation.
[GaussianBarnesCanonicalPrefactorUniformApartness](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorUniformApartness.lean)

An explicit lower modulus depends only on the disk radius and chosen negative integer. It applies to the exact local coefficient program at every sufficiently late observation across the whole admitted rational neighborhood.
[GaussianBarnesCanonicalDeflatedValueUniformApartness](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedValueUniformApartness.lean)

The shifted original translated powers telescope to the plain Gamma denominator product and one endpoint power. The exact finite identity admits zeros and supplies the polynomial part of the Barnes functional equation.
[GaussianBarnesWeightedProductShift](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesWeightedProductShift.lean), [GaussianBarnesCanonicalPolynomialShift](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalPolynomialShift.lean)

The actual change of the original local logarithm has a certified relative Mercator argument. The native input perturbation determines its rational bound and the product identity of the bases.
[GaussianBarnesCanonicalRelativeStep](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeStep.lean)

The relative-argument expansion has explicit summable quadratic and cubic error bounds on the original finite rational samples, with the original perturbation and factor index retained.
[GaussianBarnesCanonicalRelativeTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeTaylor.lean)

Exact original factor conjugation folds through each finite segment, preserving both original normalization clocks and allowing both empty segments and vanishing factors.
[GaussianNamedFiniteProductConjugation](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteProductConjugation.lean), [GaussianBarnesCanonicalHeadConjugation](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadConjugation.lean)

The actual relative quadratic term and direct exponent correction cancel to the literal first-derivative expression times the input increment plus the original controlled quadratic remainder. The named row binding and cofinal first-order estimate below carry this remainder into the original observations.
[GaussianBarnesCanonicalDerivativeAlgebra](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeAlgebra.lean)

The actual prefactor preserves conjugation through its real constants and original exponentials. The exact Gaussian rational isometry also preserves independent observation rates for any original pair of conjugated names.
[GaussianBarnesCanonicalPrefactorConjugation](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorConjugation.lean), [GaussianNamedRateConjugation](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedRateConjugation.lean)

The actual literal finite product commutes with conjugation. Comparing both cofinal values with that same finite cutoff and removing independent rational slack proves exact conjugation of the original value at Gaussian rational arguments.
[GaussianBarnesCanonicalPrefixConjugation](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalPrefixConjugation.lean), [GaussianBarnesCanonicalValueConjugation](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalValueConjugation.lean)

The original named Barnes evaluator commutes with conjugation on regular Gaussian complex names with independent disk certificates. The proof uses one common late input observation, the rational conjugation identity, and exact removal of observation slack.
[GaussianBarnesCanonicalNamedConjugation](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedConjugation.lean)

A finite exact telescope bounds the difference of two literal Gaussian rational sums when each row has an inverse-square error and a common clock error.
[GaussianReciprocalSquareSumDistance](Lean/IPRADerivations/Analysis/Series/ReciprocalSquares/GaussianReciprocalSquareSumDistance.lean)

The difference of the original Barnes exponent corrections at consecutive arguments sums exactly to the literal harmonic expression, including at empty cutoff.
[GaussianBarnesCanonicalCorrectionShift](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalCorrectionShift.lean)

The actual two named cubic logarithm observations differ from their literal linear term by the summable quadratic bound. The original rationals and both observation clocks are retained.
[GaussianNamedConstantRateFromSlack](Lean/IPRADerivations/Analysis/Names/Rates/GaussianNamedConstantRateFromSlack.lean), [GaussianBarnesCanonicalDerivativeBinding](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeBinding.lean)

The named row difference is the literal linear term plus a named relative cubic and explicit quadratic correction. This remainder has the exact independent-clock bound against zero.
[GaussianBarnesCanonicalNamedTaylorRemainder](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalNamedTaylorRemainder.lean)

The two original finite logarithms differ from the input increment times the literal first-derivative sum by the exact finite reciprocal-square bound. The actual derivative prefix and its cofinal sampler also have an explicit independent-clock rate.
[GaussianBarnesCanonicalDerivativeInterval](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeInterval.lean), [GaussianBarnesCanonicalDerivativeCofinalRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeCofinalRate.lean)

The literal shifted finite head times the plain product equals the original head times the final translated power and the exact harmonic exponential correction. The identity admits zero factors and separate disk certificates.
[GaussianBarnesCanonicalBaseProductShift](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalBaseProductShift.lean), [GaussianNamedFiniteConstantFolds](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedFiniteConstantFolds.lean), [GaussianBarnesCanonicalHeadExponentialFactors](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadExponentialFactors.lean), [GaussianBarnesCanonicalHeadShift](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadShift.lean)

The literal finite products and cofinal rate give an explicit common-disk input demand for the actual exponential tail sampler.
[GaussianBarnesCanonicalTailContinuity](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTailContinuity.lean)

The two retained finite ranges of the actual head give an explicit common-disk Lipschitz bound for the original skipped product.
[GaussianBarnesCanonicalDeflatedHeadLipschitz](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedHeadLipschitz.lean)

Combining the actual prefactor, multiplier, skipped head and cofinal tail gives an explicit uniform input demand for the exact deflated coefficient.
[GaussianBarnesCanonicalDeflatedValueContinuity](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedValueContinuity.lean)

The original cofinal log difference and original named product of the literal step with the cofinal rational derivative series have the independent rate `(3R+342)H²/(B² N₀)` plus two dyadic observation errors, with `N₀ = max(1,2R)`. The cutoff is shared only in the finite proof. The actual observations use independent clocks.
[GaussianBarnesCanonicalDerivativeTailBinding](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeTailBinding.lean)

In iPRA the actual Barnes prefactor shifts by the exponential of the literal named exponent difference, the original finite prefix obeys the cleared unit shift including zeros, and the accompanying polynomial is the original Gamma Euler head at the matching index times the exact factorial.
[GaussianBarnesCanonicalPrefactorShift](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorShift.lean), [GaussianBarnesCanonicalPrefixShift](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalPrefixShift.lean), [GaussianBarnesCanonicalGaussDenominator](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalGaussDenominator.lean)

The primitive-recursive sampler uses the verified rational deflated evaluator at its certified input demand, with constructive Cauchy regularity and properness. On the certified half-unit disk about a Barnes zero it retains a uniform apartness bound.
[GaussianBarnesCanonicalDeflatedNamed](Lean/IPRADerivations/Analysis/Barnes/Deflation/GaussianBarnesCanonicalDeflatedNamed.lean)

The normalized sampler reads the genuine translated integer power of a late original input sample. The certified half-unit disk supplies a unit bound and a finite comparison to the power at a shared late clock.
[GaussianBarnesCanonicalNamedTranslatedPower](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedTranslatedPower.lean)

The original named Barnes evaluator agrees at independent precisions with the named product of the translated power and the original named deflated coefficient. The same iPRA theorem gives uniform apartness of the coefficient on the certified half-unit disk.
[GaussianBarnesCanonicalNamedLocalFactorization](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedLocalFactorization.lean)

The difference of the two original tail exponential names agrees to quadratic error with the Gaussian step times the named product of the base tail exponential and its cofinal log derivative. Input margins guarantee a uniformly small actual logarithmic increment.
[GaussianBarnesCanonicalTailExponentialMargin](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTailExponentialMargin.lean), [GaussianBarnesCanonicalTailExponentialDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalTailExponentialDerivative.lean)

For nonzero rational Gaussian steps the actual divided differences approach the original cofinal derivative names with leading errors linear in the step size. Each comparison has a closed iPRA dyadic precision theorem retaining two independent observations. The exponential derivative uses the named product of the base tail exponential and the logarithmic derivative.
[GaussianRationalConstantProductRate](Lean/IPRADerivations/Analysis/Names/Rates/GaussianRationalConstantProductRate.lean), [GaussianNativeDerivativeQuotientRate](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNativeDerivativeQuotientRate.lean), [GaussianBarnesCanonicalLogDerivativeQuotient](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalLogDerivativeQuotient.lean), [GaussianBarnesCanonicalTailExponentialQuotient](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTailExponentialQuotient.lean)

The exact product split applies to the original quotient by a literal rational Gaussian step. Independent quotient and continuity rates for the two factors give the product derivative rate with a common denominator, including at zeros of either factor.
[GaussianNamedNativeProductDerivativeRate](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNamedNativeProductDerivativeRate.lean)

The actual terminal logarithm, harmonic difference and Stirling remainder give a uniform bound `(R²+M+1)/K+(17M+18)2⁻ᵖ` at cutoff K under the certified disk and coefficient bounds.
[GaussianBarnesCanonicalTerminalRemainder](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTerminalRemainder.lean), [GaussianBarnesCanonicalHarmonicRemainder](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalHarmonicRemainder.lean), [GaussianBarnesCanonicalCombinedRemainder](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalCombinedRemainder.lean)

The literal finite rational correction has an exact linear term and a quadratic remainder bounded by `N H²/B²` for a native Gaussian step of size at most `H/B`.
[GaussianBarnesCanonicalHeadCorrectionDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadCorrectionDerivative.lean)

The actual kept base-power product agrees with a rational coefficient polynomial at every Gaussian rational argument. Its value, slope, and quadratic remainder have uniform certified bounds and the estimate includes zeros.
[GaussianBarnesCanonicalHeadPolynomial](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadPolynomial.lean), [GaussianBarnesCanonicalHeadPolynomialDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadPolynomialDerivative.lean)

The actual full Barnes divided difference has a uniform rate once the original fixed prefix quotient is supplied. The join uses the checked disk continuity of the fixed prefix and the closed tail exponential derivative, retaining both independent observation errors.
[GaussianBarnesCanonicalValueDerivativeJoin](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalValueDerivativeJoin.lean)

The exponential of the actual combined logarithmic remainder approaches the exact constant one at independent precisions and uniform leading rate `factor(radius R M)*(R²+M+1)/K`. The translated input and midpoint have uniformly certified rational disk bounds.
[GaussianBarnesCanonicalCombinedRemainderRate](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalCombinedRemainderRate.lean), [GaussianBarnesCanonicalShiftChart](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalShiftChart.lean)

The actual named prefactor exponent difference is exactly `S−1/2−(1+γ)*(z+1/2)`, with the original Stirling and Euler constants and their certified arithmetic.
[GaussianBarnesCanonicalPrefactorShiftAlgebra](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorShiftAlgebra.lean), [GaussianBarnesCanonicalPrefactorShiftBinding](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorShiftBinding.lean)

Equal Gaussian fractions on a fixed certified disk give identical cofinal logarithmic-derivative observations at a common precision. The original named Barnes quotient agrees with the native rational quotient under exact rational endpoint and step equivalences, including independently chosen endpoint disks.
[GaussianBarnesCanonicalDerivativeFractionProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeFractionProperness.lean), [GaussianBarnesCanonicalNamedQuotientBinding](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedQuotientBinding.lean)

The actual dynamic-radius finite exponential has the named derivative equal to that exponential times the exact finite correction slope. The independent first-order bound is quadratic in the native Gaussian step and its coefficients depend only on the disk and cutoff.
[GaussianNamedExponentialTaylorTransport](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedExponentialTaylorTransport.lean), [GaussianBarnesCanonicalHeadCorrectionExponentialDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.lean)

The original finite recurrence exponent and actual terminal power are matched to the combined named remainder. The adjacent Euler logarithm has an independent `1/N` bound, preserving the difference between the actual Gauss cutoff and the Barnes recurrence cutoff.
[GaussianBarnesCanonicalNormalizedExponentAlgebra](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalNormalizedExponentAlgebra.lean), [GaussianBarnesCanonicalAdjacentLog](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalAdjacentLog.lean), [GaussianBarnesCanonicalNormalizedExponent](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalNormalizedExponent.lean), [GaussianBarnesCanonicalTerminalPower](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalTerminalPower.lean)

The actual Barnes prefactor has the named derivative given by the original prefactor times its named exponent slope. On a certified disk the independent-clock first-order error is quadratic in the step, with precisely the original named Stirling and Euler constants.
[GaussianBarnesCanonicalPrefactorExponentDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefactorExponentDerivative.lean), [GaussianBarnesCanonicalPrefactorExponentEstimate](Lean/IPRADerivations/Analysis/Barnes/Prefactors/GaussianBarnesCanonicalPrefactorExponentEstimate.lean), [GaussianBarnesCanonicalPrefactorDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefactorDerivative.lean)

Equivalent Gaussian fractions on one certified disk give equivalent actual cofinal tail exponential names and therefore equivalent actual tail derivative names at independent precisions.
[GaussianBarnesCanonicalTailDerivativeFractionProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalTailDerivativeFractionProperness.lean)

The actual finite head quotient converges to the sum of the original correction exponential derivative times the exact polynomial and the original exponential times the polynomial slope. The leading error is uniform on a disk, applies at zeros of the head, and scales linearly with the native Gaussian step.
[GaussianNativeDerivativeQuotientQuadratic](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNativeDerivativeQuotientQuadratic.lean), [GaussianBarnesCanonicalHeadPolynomialQuotient](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadPolynomialQuotient.lean), [GaussianBarnesCanonicalHeadDerivativeJoin](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadDerivativeJoin.lean), [GaussianBarnesCanonicalHeadDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadDerivative.lean)

The derivative of the actual prefactor times the original kept head has a uniform first-order quotient rate with denominator `B*initial R`. The proof keeps both original named factors and allows all zeros of the head.
[GaussianBarnesCanonicalPrefixDerivativeJoin](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefixDerivativeJoin.lean), [GaussianBarnesCanonicalPrefixDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefixDerivative.lean)

Equivalent fractions give identical data for the actual prefactor derivative sampler and equivalent output names at independent precisions.
[GaussianBarnesCanonicalPrefactorDerivativeProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefactorDerivativeProperness.lean)

A rational input distance bound `A/M` on a common certified disk gives a uniform leading derivative error `gain(R) A/M` for the original independent observations.
[GaussianBarnesCanonicalPrefactorDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefactorDerivativeContinuity.lean)

The original full Barnes value quotient converges to its explicit product-rule derivative name, with independent observations and a uniform bound linear in the step size. The same bound applies to the actual named quotient for names representing the corresponding rational configuration.
[GaussianBarnesCanonicalValueDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalValueDerivative.lean)

At every admitted Gaussian rational point explicit denominator refinement permits a nonzero arbitrarily small native step. Full derivative fraction properness gives independent comparison to a fixed name at the original argument, including arbitrarily requested internal precision.
[GaussianBarnesCanonicalHeadDerivativeFractionProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadDerivativeFractionProperness.lean), [GaussianBarnesCanonicalDerivativeStep](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeStep.lean), [GaussianBarnesCanonicalValueDerivativeProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalValueDerivativeProperness.lean)

One refined nonzero rational step works simultaneously in two certified interior disks. Exact properness of the actual Barnes values and removal of dyadic slack identify the two original derivative names.
[GaussianBarnesCanonicalDerivativeDiskIndependence](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeDiskIndependence.lean)

The cofinal logarithmic slope has Lipschitz constant `4(R+R²)` on a certified disk. The actual tail exponential derivative then has an explicit primitive-recursive input modulus at independent precisions.
[GaussianBarnesCanonicalDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeContinuity.lean), [GaussianBarnesCanonicalTailExponentialDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalTailExponentialDerivativeContinuity.lean)

At a common positive cutoff, the original Barnes truncations satisfy the finite recurrence with the original Gauss reciprocal approximation and the matched exponential remainder times `1+w/K`. The cleared identity allows Gamma poles and zeros of the Barnes factors.
[GaussianBarnesCanonicalGaussNormalizers](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalGaussNormalizers.lean), [GaussianBarnesCanonicalNormalizedMultiplier](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalNormalizedMultiplier.lean), [GaussianBarnesCanonicalFiniteGaussIdentity](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalFiniteGaussIdentity.lean)

Comparing the actual padded synthetic quotients and finite harmonic correction gives a disk Lipschitz bound for the original kept head derivative at arbitrary Gaussian rational presentations. The same program has an explicit uniform bound on every sample.
[GaussianRationalSyntheticSlopeLipschitz](Lean/IPRADerivations/Analysis/Inequalities/GaussianRationalSyntheticSlopeLipschitz.lean), [GaussianBarnesCanonicalHeadCorrectionContinuity](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalHeadCorrectionContinuity.lean), [GaussianBarnesCanonicalHeadDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalHeadDerivativeContinuity.lean)

A uniform Lipschitz bound and all-sample cap for the original kept-prefix derivative follow from the checked head and prefactor bounds and the actual named sum and product observation laws.
[GaussianNamedBoundedSumObservation](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedBoundedSumObservation.lean), [GaussianBarnesCanonicalPrefixDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalPrefixDerivativeContinuity.lean)

Given a checked primitive-recursive disk modulus, the genuine lifted sampler evaluates the original rational derivative at a late original input observation. It has closed iPRA regularity, common-disk properness, and an explicit late-readback bound.
[GaussianNamedDiskDemandLift](Lean/IPRADerivations/Analysis/Geometry/DiskNames/GaussianNamedDiskDemandLift.lean), [GaussianNamedDiskDemandReadback](Lean/IPRADerivations/Analysis/Geometry/DiskNames/GaussianNamedDiskDemandReadback.lean), [GaussianBarnesCanonicalNamedDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalNamedDerivative.lean)

The original full rational derivative has a primitive-recursive uniform disk modulus. It gives the actual derivative sampler on regular Gaussian names, with regularity, properness across separately certified radii, explicit late readback, and the original quotient rate on exact rational configurations.
[GaussianBarnesCanonicalValueDerivativeContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalValueDerivativeContinuity.lean), [GaussianBarnesCanonicalNamedValueDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalNamedValueDerivative.lean)

For $F(z)=G(1+z)$, the actual entire reciprocal Gamma name gives the cleared recurrence $F(z+1) / \Gamma(z+1)=F(z)$ on every admitted Gaussian rational, including poles. Multiplying by the original Gamma name on the certified pole-free domain gives the ordinary recurrence.
[GaussianBarnesCanonicalFiniteGaussRate](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalFiniteGaussRate.lean), [GaussianBarnesCanonicalFunctionalEquation](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalFunctionalEquation.lean), [GaussianBarnesCanonicalPoleFreeRecurrence](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalPoleFreeRecurrence.lean)

A single dyadic upper bound on the native step pays the original quotient margin and desired output precision, independently of the nonzero certificate.
[GaussianBarnesCanonicalDerivativeIncrementPrecision](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalDerivativeIncrementPrecision.lean)

The actual quotient by an apart regular named Gaussian step agrees to an explicit independent rate with the native quotient at a decoded late step. The error keeps the individual endpoint approximation rates and the actual reciprocal clock.
[GaussianNamedIncrementQuotientFrozenRate](Lean/IPRADerivations/Analysis/Names/Rates/DifferenceQuotients/GaussianNamedIncrementQuotientFrozenRate.lean)

The original base and late apart step have exact common-denominator native encodings and a matched exact sum. The actual named addition clock is retained, and rational step bounds give native smallness certificates.
[GaussianNamedIncrementChart](Lean/IPRADerivations/Analysis/Names/Differences/GaussianNamedIncrementChart.lean)

An explicit mixed-denominator disk modulus gives a genuine named sampler for the original C7 evaluator. The named output is regular and proper, and its comparison to the frozen rational evaluation preserves independent clocks, including at poles.
[GaussianGammaC7Named](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaC7Named.lean), [GaussianGammaC7NamedFrozen](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaC7NamedFrozen.lean)

The actual named base and shifted values both have an independent leading error of one dyadic unit at the requested precision in their comparison with the shared late rational chart. Changing the step denominator on this chart preserves the actual quotient datum exactly.
[GaussianBarnesCanonicalNamedIncrementEndpoints](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedIncrementEndpoints.lean)

The actual named divided difference converges to the actual named derivative for apart regular Gaussian increments with a certified dyadic sample bound. The requested step bound depends only on the disk and target precision. The apartness certificate determines only the later observation clock.
[GaussianBarnesCanonicalNamedIncrementDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/FirstDerivative/GaussianBarnesCanonicalNamedIncrementDerivative.lean)

The original first-derivative row increments by the actual rational second derivative times the step, with exact resolvent remainder and uniform bound `8H²/(B²k²)`. The second-derivative row has radius `12R/k²` and its original finite sums obey the inverse-square telescope.
[GaussianBarnesCanonicalSecondDerivativeRow](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeRow.lean), [GaussianBarnesCanonicalSecondDerivativeTail](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeTail.lean), [GaussianBarnesCanonicalSecondDerivativeStep](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeStep.lean)

When a regular input name represents an exact Gaussian rational, the original named reciprocal Gamma value agrees with the original rational C7 evaluator at independent observation precisions. The proof applies at poles.
[GaussianGammaC7NamedRationalBinding](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaC7NamedRationalBinding.lean)

At every internal order r≥3 the rational coefficient through the original base reciprocal has the bound `2^r/(r*k^(r−1))`. Exact multiplication by r! gives the factorial-scaled row with its sharp bound. Both programs have inverse-square bounds for finite tails.
[GaussianBarnesCanonicalHigherRows](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherRows.lean)

The original Barnes and reciprocal-Gamma evaluators on the actual named unit shift satisfy the cleared functional equation at every regular Gaussian input on a certified disk. The proof aligns their late rational observations and passes the exact rational equation through independent dyadic rate bounds.
[GaussianBarnesCanonicalNamedFunctionalEquation](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedFunctionalEquation.lean)

On certified pole-free regular Gaussian input charts, multiply the cleared Barnes equation by the original named Gamma evaluator. Its exact inverse relation with the original named reciprocal-Gamma yields the usual functional equation.
[GaussianGammaC7NamedInverse](Lean/IPRADerivations/Analysis/Gamma/FunctionalEquations/ReciprocalGamma/GaussianGammaC7NamedInverse.lean), [GaussianBarnesCanonicalNamedPoleFreeRecurrence](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedPoleFreeRecurrence.lean)

Starting at the original retained-row boundary, the exact rational reciprocal-square rows define a regular second derivative name. The original cofinal first derivative has that derivative with the stated independent-clock quadratic increment bound. At apart encoded rational steps the native difference quotient converges with leading error 16 times the step norm divided by the original head boundary.
[GaussianScaledReciprocalSquareInterval](Lean/IPRADerivations/Analysis/Series/ReciprocalSquares/GaussianScaledReciprocalSquareInterval.lean), [GaussianBarnesCanonicalSecondDerivativeCofinal](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeCofinal.lean), [GaussianBarnesCanonicalSecondDerivativeInterval](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeInterval.lean), [GaussianBarnesCanonicalSecondDerivativeBinding](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalSecondDerivativeBinding.lean)

The literal finite Mercator polynomials have a geometric remainder at every internal order. The same bound, with the rounded sampler allowance, controls the original named logarithm. At the original Barnes shifted relative input the bound uses the certified radius 2H/(Bk).
[GaussianFiniteLogarithmTaylorRemainder](Lean/IPRADerivations/Analysis/Logarithm/FiniteSeries/GaussianFiniteLogarithmTaylorRemainder.lean), [GaussianLocalLogarithmTaylorRemainder](Lean/IPRADerivations/Analysis/Logarithm/Local/GaussianLocalLogarithmTaylorRemainder.lean), [GaussianBarnesCanonicalRelativeMercatorRemainder](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeMercatorRemainder.lean)

At every internally encoded order r at least three, the literal retained rational coefficient sums define a regular name with independent-clock finite-prefix error bounded by 2^r divided by the retained boundary. The proof splits the literal finite sums and applies the same inverse-square telescope at every encoded order.
[GaussianBarnesCanonicalHigherTail](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherTail.lean), [GaussianBarnesCanonicalHigherCofinal](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherCofinal.lean), [GaussianBarnesCanonicalHigherCofinalRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherCofinalRate.lean)

At every encoded order at least three, the original relative logarithm term multiplied by the Barnes row index equals the factorial-normalized coefficient times the literal displacement raised to that degree. The proof uses the checked inverse of the original base and the actual parity and radius powers.
[GaussianBarnesCanonicalHigherRelative](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherRelative.lean)

The literal finite base-power product equals its displacement polynomial, including at zeros. Every truncation through the actual degree has error controlled by a computed Horner mass times the displacement radius to the first omitted power.
[GaussianBarnesCanonicalCenteredHead](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCenteredHead.lean), [GaussianBarnesCanonicalCenteredHeadTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCenteredHeadTaylor.lean)

Scaling each higher logarithmic coefficient sum by the encoded factorial gives the literal derivative-row sum. The normalized cofinal name is regular and each actual sample equals that derivative sum at its own explicit finite cutoff.
[GaussianBarnesCanonicalHigherDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherDerivative.lean)

The original corrected log-row increment and the literal finite retained interval compare to their actual Mercator-based Taylor polynomials at every internally encoded degree at least two. The interval error retains the exact inverse-square telescoping factor for all lengths.
[GaussianBarnesCanonicalCorrectedMercator](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalCorrectedMercator.lean), [GaussianBarnesCanonicalCorrectedMercatorInterval](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalCorrectedMercatorInterval.lean)

The literal weighted Mercator polynomial splits at degree two. The exact low terms are the original derivative rows with their finite correction, and the higher terms transpose from logarithmic rows to the original retained coefficient-prefix sums.
[GaussianBarnesCanonicalHigherMercatorSum](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherMercatorSum.lean), [GaussianBarnesCanonicalQuadraticBinding](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalQuadraticBinding.lean), [GaussianBarnesCanonicalHigherMercatorTranspose](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalHigherMercatorTranspose.lean)

The kept base-power product has a quantitative zero-free Mercator chart. Its relative logarithm combines with the original finite correction, prefactor exponent and cofinal logarithmic tail. On those charts, exponentiating the sum and multiplying by the original starting value restores the original shifted value. The kept powers also have the stated uniform cubic polynomial remainder.
[GaussianBarnesCanonicalHeadRelativeLog](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalHeadRelativeLog.lean), [GaussianBarnesCanonicalHeadRelativeLogMargin](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalHeadRelativeLogMargin.lean), [GaussianRationalUniformSecondOrderPolynomial](Lean/IPRADerivations/Analysis/Polynomials/Taylor/GaussianRationalUniformSecondOrderPolynomial.lean), [GaussianBarnesCanonicalHeadPolynomialTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalHeadPolynomialTaylor.lean), [GaussianBarnesCanonicalRelativeLogIncrement](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeLogIncrement.lean)

The corrected finite interval Mercator polynomial is exactly the sum of the original retained first, second, and higher coefficient blocks times their displacement powers. The original finite named increment therefore has the checked arbitrary-order Taylor bound for that coefficient polynomial.
[GaussianBarnesCanonicalCorrectedMercatorCoefficients](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalCorrectedMercatorCoefficients.lean), [GaussianBarnesCanonicalCorrectedMercatorPrefix](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalCorrectedMercatorPrefix.lean)

The original cofinal logarithmic increment admits the literal corrected finite Taylor polynomial with a combined finite-prefix and summable Taylor error. Its primitive-recursive cutoff makes the finite-prefix contribution dyadic and retains the analytic remainder at every encoded degree at least two.
[GaussianBarnesCanonicalCorrectedMercatorCofinal](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalCorrectedMercatorCofinal.lean)

The original value equals the literal finite base-power product times the named exponential of the actual prefactor exponent, finite correction and cofinal log. On a shifted rational chart the kept product is its exact centered displacement polynomial. Both identities hold at zeros of the head.
[GaussianBarnesCanonicalSingleExponential](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalSingleExponential.lean)

The original shifted value is the exact centered kept polynomial times the exponential of the central exponent times the exponential of its actual named increment. Any independent-clock rate for the last factor lifts to the original shifted Barnes evaluator with a gain independent of the displacement.
[GaussianBarnesCanonicalCenteredExponentialShift](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCenteredExponentialShift.lean), [GaussianBarnesCanonicalCenteredProductRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCenteredProductRate.lean)

The original Barnes exponent has an explicit finite rational coefficient buffer and a checked Horner representation. On a certified zero-free chart the actual local logarithmic increment has a cubic comparison with the fixed cofinal first and second derivative names. Exponential and stored-product estimates provide the quantitative transfer from the original exponent approximation to the centered Barnes value.
[GaussianNamedSumDifference](Lean/IPRADerivations/Analysis/Names/FiniteOperations/GaussianNamedSumDifference.lean), [GaussianBarnesCanonicalExponentTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylor.lean), [GaussianBarnesCanonicalExponentTaylorFrozen](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorFrozen.lean), [GaussianBarnesCanonicalExponentTaylorBuffer](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorBuffer.lean), [GaussianBarnesCanonicalExponentTaylorBufferEvaluation](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorBufferEvaluation.lean), [GaussianLocalLogarithmQuadraticRate](Lean/IPRADerivations/Analysis/Logarithm/Local/GaussianLocalLogarithmQuadraticRate.lean), [GaussianBarnesCanonicalHeadRelativeLogTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalHeadRelativeLogTaylor.lean), [GaussianBarnesCanonicalRelativeExponentTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeExponentTaylor.lean), [GaussianBarnesCanonicalRelativeLogTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeLogTaylor.lean), [GaussianBarnesCanonicalTailQuadraticName](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalTailQuadraticName.lean), [GaussianBarnesCanonicalRelativeLogFixedTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/RelativeExpansions/GaussianBarnesCanonicalRelativeLogFixedTaylor.lean), [GaussianNamedExponentialRateFromConstant](Lean/IPRADerivations/Analysis/Exponential/Names/GaussianNamedExponentialRateFromConstant.lean), [GaussianRationalPolynomialExponentialRecomposition](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialRecomposition.lean), [GaussianRationalPolynomialProductTruncation](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianRationalPolynomialProductTruncation.lean), [GaussianBarnesCanonicalTaylorRecomposition](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalTaylorRecomposition.lean)

The original Barnes evaluator admits one stored degree-m Taylor polynomial at every encoded order m at least two on a certified small rational ball. Its coefficient clocks are independent of the queried displacement. The value estimate has explicit order-m-plus-one error and a dyadic coefficient allowance. Evaluations at the same rational point compare with the sum of the two errors, including at kept-head zeros. The exponent coefficient mass weighted at radius 1/4 is uniform across orders, and the generic exponential recomposition estimate supports that weighting.
[GaussianPolynomialLowPrefixMass](Lean/IPRADerivations/Analysis/Polynomials/Products/GaussianPolynomialLowPrefixMass.lean), [GaussianRationalPolynomialExponentialProductTruncation](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialProductTruncation.lean), [GaussianBarnesCanonicalExponentTaylorMass](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorMass.lean), [GaussianBarnesCanonicalExponentTaylorHorner](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorHorner.lean), [GaussianBarnesCanonicalExponentTaylorSchedule](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorSchedule.lean), [GaussianBarnesCanonicalExponentTaylorBallSchedule](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorBallSchedule.lean), [GaussianBarnesCanonicalTaylorProduct](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProduct.lean), [GaussianBarnesCanonicalTaylorBall](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalTaylorBall.lean), [GaussianBarnesCanonicalTaylorBallOverlap](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalTaylorBallOverlap.lean), [GaussianBarnesCanonicalTaylorBallSource](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalTaylorBallSource.lean), [GaussianBarnesCanonicalExponentTaylorWeightedMass](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorWeightedMass.lean), [GaussianRationalPolynomialExponentialDilation](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialDilation.lean), [GaussianRationalPolynomialExponentialFixedRadius](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialFixedRadius.lean)

One positive step radius given by the reciprocal of the divisor for the center disk supports all encoded degrees at least two. The proof uses the original stored Taylor polynomial and observation schedule and bounds the analytic error in powers of the scaled displacement. The same ball estimates compare evaluations from different centers, clocks, and degrees at an equal Gaussian rational input, including kept-head zeros. Fixed-order derivatives of the original finite partial products still require a convergence proof.
[GaussianRationalPolynomialExponentialWeightedProductTruncation](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianRationalPolynomialExponentialWeightedProductTruncation.lean), [GaussianBarnesCanonicalWeightedTaylorRecomposition](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorRecomposition.lean), [GaussianBarnesCanonicalWeightedTaylorProduct](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorProduct.lean), [GaussianBarnesCanonicalWeightedTaylorBallSource](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBallSource.lean), [GaussianBarnesCanonicalWeightedTaylorBall](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBall.lean), [GaussianBarnesCanonicalWeightedTaylorBallOverlap](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBallOverlap.lean)

The literal constant, linear, quadratic and higher entries compare at independently chosen prefactor precisions, finite tail cutoffs and retained degrees. At a fixed degree, explicit cutoffs give a common dyadic rate for the actual coefficient difference and its coefficient norm. These estimates concern the original exponent buffers and provide the input for finite exponential coefficient variation.
[GaussianBarnesCanonicalExponentTaylorCoefficientCauchy](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.lean), [GaussianBarnesCanonicalExponentTaylorRetainedCoefficient](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.lean), [GaussianBarnesCanonicalExponentTaylorCoefficientMassGap](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorCoefficientMassGap.lean)

At any fixed retained degree, the original finite exponential coefficient variation and exact convolution with the kept Barnes head give an explicit dyadic Cauchy bound at every retained coefficient. Prefactor precisions and tail cutoffs may vary independently. Zero padding handles coefficients above the degree of the kept head. The original central exponential scalar and identification with actual derivatives remain to be incorporated.
[GaussianBarnesCanonicalTaylorProductCoefficientCauchy](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductCoefficientCauchy.lean)

The original literal shifted partial product equals the exact centered kept powers times its finite central scalar and the exponential of its actual finite increment. The fixed-cutoff increment uses the original stored Taylor buffer and a prefactor clock independent of the cutoff. The finite scalar approaches the original cofinal scalar at independent observation clocks with an explicit dyadic cutoff.
[GaussianBarnesCanonicalFiniteCentralExponential](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteCentralExponential.lean), [GaussianBarnesCanonicalFiniteExponentTaylor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFiniteExponentTaylor.lean), [GaussianBarnesCanonicalFiniteCenteredExponentialShift](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteCenteredExponentialShift.lean)

The original Taylor-ball error admits separate dyadic bounds in observation precision and Taylor degree with gains independent of the queried displacement and degree. At a fixed prefactor precision and tail cutoff each retained Taylor product coefficient is exactly independent of the retained degree. Regular cofinal coefficient names and their factorially scaled versions with the original central scalar have computable dyadic comparison to the corresponding stored finite coefficients with the actual finite central scalar. Identification with iterated derivatives and the fixed-cutoff derivative samplers are still open.
[GaussianBarnesCanonicalWeightedTaylorBallDyadic](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBallDyadic.lean), [GaussianPolynomialExponentialLowJet](Lean/IPRADerivations/Analysis/Exponential/Polynomials/GaussianPolynomialExponentialLowJet.lean), [GaussianBarnesCanonicalTaylorProductOrderInvariance](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductOrderInvariance.lean), [GaussianBarnesCanonicalTaylorProductCoefficientName](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductCoefficientName.lean), [GaussianBarnesCanonicalTaylorProductDerivativeName](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductDerivativeName.lean), [GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.lean)

The literal adjacent-subtraction grid program agrees with iterated translated differences of a stored polynomial. On the Gaussian rational grid its terminal value is the leading coefficient multiplied by the encoded factorial and the corresponding step power. The degree, grid step and coefficients are object-language inputs. This supplies the polynomial identity required for identifying Barnes Taylor coefficients with higher derivative observations.
[GaussianPolynomialForwardDifference](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifference.lean), [GaussianPolynomialForwardDifferenceIteration](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceIteration.lean), [GaussianPolynomialForwardDifferenceGrid](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGrid.lean)

At every finite cutoff, including zero, retiming the original prefactor alone gives regular names for the stored Taylor coefficients. The factorially scaled versions with the actual finite central scalar converge to the corresponding cofinal names at an explicit dyadic rate, with independently chosen observation clocks. Both families are exactly invariant under a change of retaining degree. The literal shifted finite product has a weighted Taylor-ball value rate with a cutoff-independent error. Its identification by higher derivative observations and a cutoff uniform over the whole center disk are separate remaining obligations.
[GaussianBarnesCanonicalFiniteCentralExponentialBound](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteCentralExponentialBound.lean), [GaussianBarnesCanonicalFiniteWeightedTaylorValue](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteWeightedTaylorValue.lean), [GaussianBarnesCanonicalExponentTaylorFixedCutoff](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorFixedCutoff.lean), [GaussianBarnesCanonicalTaylorProductFixedCutoff](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductFixedCutoff.lean), [GaussianBarnesCanonicalFixedTaylorCoefficientName](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorCoefficientName.lean), [GaussianBarnesCanonicalFixedTaylorDerivativeName](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorDerivativeName.lean), [GaussianBarnesCanonicalTaylorDerivativeOrderInvariance](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.lean)

One finite central scalar sample and one stored Taylor polynomial give the packed Horner grid for all literal partial-product observations. The actual adjacent-subtraction program propagates row errors and division by the step power recovers the factorial-scaled leading coefficient. The same coefficient is read by the regular fixed-cutoff name, giving a quantitative comparison at independent observation clocks. The finite Taylor radius splits into analytic and clock terms. The central scalar, head coefficients, and raw cofinal coefficient Cauchy rates have bounds uniform on the center disk. The normalized small-step convergence theorem and the iterated derivative identification remain open.
[GaussianPolynomialForwardDifferenceGridError](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridError.lean), [GaussianPolynomialForwardDifferenceNormalization](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceNormalization.lean), [GaussianBarnesCanonicalFiniteTaylorGrid](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGrid.lean), [GaussianBarnesCanonicalFiniteTaylorGridObservations](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridObservations.lean), [GaussianBarnesCanonicalFiniteTaylorGridLeading](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridLeading.lean), [GaussianBarnesCanonicalFiniteTaylorGridComparison](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridComparison.lean), [GaussianBarnesCanonicalFiniteTaylorGridBudget](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridBudget.lean), [GaussianBarnesCanonicalCentralUniformBound](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCentralUniformBound.lean), [GaussianBarnesCanonicalHeadUniformMass](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalHeadUniformMass.lean), [GaussianBarnesCanonicalTaylorProductUniformGap](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductUniformGap.lean)

At every encoded order at least two, the actual normalized forward grid of a literal finite Barnes partial product has a dyadic comparison with the fixed-cutoff factorially scaled Taylor name on an admitted native chart. The sufficient step threshold depends on the center and chart denominator. The fractional lower norm of the native step cancels all but one displacement power. The step budget is independent of the finite cutoff and of a separate apartness witness. Explicit later literal observation clocks pay all sample allowances, while the fixed name is observed at an independent clock.
[GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.lean), [GaussianBarnesCanonicalFiniteTaylorGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridLimit.lean)

The original fixed-cutoff and cofinal coefficient names have a dyadic independent-clock rate at a cutoff depending only on the disk, retained degree, coefficient order, and requested precision. The same property holds for their factorially scaled names with the actual central scalars. On an admitted native chart the normalized literal finite grid has the stated comparison with the cofinal coefficient name, and the encoded difference program has its exact increment recurrence. Uniformity of the step threshold under changes of native denominator and identification with iterated derivatives still require proof.
[GaussianBarnesCanonicalFixedTaylorUniformConvergence](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorUniformConvergence.lean), [GaussianBarnesCanonicalTaylorProductUniformMass](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductUniformMass.lean), [GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.lean), [GaussianBarnesCanonicalCofinalTaylorGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorGridLimit.lean), [GaussianPolynomialForwardDifferenceGridIncrement](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridIncrement.lean)

The literal finite and original cofinal Barnes normalized grids have a step threshold depending only on the disk, encoded degree, and requested precision. Their grid observations use explicit later clocks independently of the target coefficient observation. Exact chart refinement preserves the rational center and produces admissible nonzero steps at arbitrarily large encoded denominators. The original forward grids for opposite steps cancel the next odd degree term, with an exact fractional error bound. Identifying the named Taylor coefficients with iterated derivatives still requires an increment theorem for the coefficient names themselves.
[GaussianBarnesCanonicalFiniteCentralDiskBound](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteCentralDiskBound.lean), [GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.lean), [GaussianBarnesCanonicalFiniteTaylorGridUniformObservations](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.lean), [GaussianBarnesCanonicalFiniteTaylorDiskGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.lean), [GaussianBarnesCanonicalCofinalTaylorGridObservations](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorGridObservations.lean), [GaussianBarnesCanonicalActualTaylorDiskGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalActualTaylorDiskGridLimit.lean), [GaussianPolynomialForwardDifferenceGridLinearity](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridLinearity.lean), [GaussianRationalHornerLeadingSplit](Lean/IPRADerivations/Analysis/Polynomials/Horner/GaussianRationalHornerLeadingSplit.lean), [GaussianPolynomialForwardDifferenceGridEven](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridEven.lean), [GaussianPolynomialForwardDifferenceGridEvenError](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridEvenError.lean)

For any equivalent Gaussian rational centers with positive denominators, the original centered head and the stored exponent and product buffers agree at the same radius, observation clock, cutoff, and degree. The fixed and cofinal normalized coefficient names agree at independent clocks. The original prefactor exponent and finite head-correction sum give identical input data to the prefix exponential. Chart independence of the finite tail and the full factorial Taylor names is a separate step.
[GaussianBarnesCanonicalCenteredHeadChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalCenteredHeadChart.lean), [GaussianBarnesCanonicalTaylorTailFraction](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorTailFraction.lean), [GaussianBarnesCanonicalExponentTaylorBufferProperness](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalExponentTaylorBufferProperness.lean), [GaussianBarnesCanonicalTaylorProductChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorProductChart.lean), [GaussianBarnesCanonicalTaylorCoefficientChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorCoefficientChart.lean), [GaussianBarnesCanonicalPrefixChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalPrefixChart.lean)

The original finite Barnes grids at opposite Gaussian rational steps cancel the next Taylor degree exactly. Uniform row bounds transfer this cancellation to the literal product samples. Readback at an independent clock identifies the target with twice the original fixed-cutoff factorial Taylor coefficient at any admitted retention order. The explicit step and clock schedule for quadratic convergence is developed separately.
[GaussianBarnesCanonicalFiniteTaylorEvenGridComparison](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridComparison.lean), [GaussianBarnesCanonicalFiniteTaylorEvenGridUniformComparison](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridUniformComparison.lean), [GaussianBarnesCanonicalFiniteTaylorEvenGridReadback](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridReadback.lean)

The actual unrounded finite logarithm rows agree at equal rational points. The original rounding estimate gives equality of the finite logarithm names at independent clocks. This transfers through the finite tail exponential and exact prefix input to the original central scalar. The original fixed and cofinal factorial Taylor names now agree across rational presentations of the same point on a common admitted disk, including zeros of the centered head.
[GaussianBarnesCanonicalLogRowFractionProperness](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogRowFractionProperness.lean), [GaussianBarnesCanonicalFiniteLogFractionProperness](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalFiniteLogFractionProperness.lean), [GaussianBarnesCanonicalFiniteCentralChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalFiniteCentralChart.lean), [GaussianBarnesCanonicalTaylorDerivativeChart](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorDerivativeChart.lean)

Explicit observation clocks make the original finite and cofinal opposite-grid outputs differ from twice the corresponding factorial Taylor coefficient samples by at most a disk-dependent gain times the square of the rational step norm. The generic adjacent-window identity gives the next-order opposite grid exactly, and a quadratic error at each endpoint becomes a linear error after dividing by the step.
[GaussianPolynomialForwardDifferenceGridEvenIncrement](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridEvenIncrement.lean), [GaussianBarnesCanonicalFiniteTaylorEvenGridBudget](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.lean), [GaussianBarnesCanonicalFiniteTaylorEvenGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.lean), [GaussianBarnesCanonicalCofinalTaylorEvenGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorEvenGridLimit.lean)

The two adjacent windows of the actual cofinal Barnes grid agree exactly with the corresponding original forward observations. The backward return matches decoded rational nodes and costs at most one dyadic unit at the scheduled observation clock. The quotient of two independently observed doubled cofinal factorial names now has a disk-uniform linear step error relative to the actual mixed next-order grid. Its identification with the next factorial Taylor name remains a separate obligation.
[GaussianBarnesCanonicalCofinalTaylorGridWindows](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorGridWindows.lean), [GaussianBarnesCanonicalCofinalTaylorGridReturn](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorGridReturn.lean), [GaussianBarnesCanonicalCofinalTaylorEvenGridWindows](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorEvenGridWindows.lean), [GaussianBarnesCanonicalCofinalTaylorGridIncrementRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorGridIncrementRate.lean)

For each retained degree at least two, the original cofinal factorial names agree across two disk radii at independent observation clocks when the center is admitted with one unit of room in each disk. One positive re-encoding provides a common nonzero step. Low degrees and disks that admit the center only on the boundary require additional radius arguments.
[GaussianBarnesCanonicalCofinalGridRadiusComparison](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalGridRadiusComparison.lean), [GaussianBarnesCanonicalTaylorDerivativeRadius](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorDerivativeRadius.lean)

The original named order-e difference quotient, read at an arbitrary clock, agrees with the mixed next-order grid at a linear step rate plus its explicit observation allowance. The opposite polynomial grids can use different origins and still recover twice the same factorial leading coefficient. Exact recentering puts the sampled backward displacements on the original native Barnes chart.
[GaussianBarnesCanonicalMixedTaylorGridGeometry](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalMixedTaylorGridGeometry.lean), [GaussianPolynomialForwardDifferenceGridOppositeCoefficient](Lean/IPRADerivations/Analysis/Polynomials/FiniteDifferences/GaussianPolynomialForwardDifferenceGridOppositeCoefficient.lean), [GaussianBarnesCanonicalTaylorNamedQuotient](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorNamedQuotient.lean)

The original degree-zero factorial Taylor name equals the canonical Barnes value at independent clocks on every admitted disk. Exact readback of the head-power constant term proves radius independence also at centers on the boundary of a disk.
[GaussianBarnesCanonicalTaylorDerivativeZero](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalTaylorDerivativeZero.lean)

The original degree-one Taylor name equals the preexisting canonical Barnes derivative at independent observation clocks on the widened admitted disk. Replacing the two degree-zero endpoints by the actual values gives the zero-to-one named difference quotient an explicit dyadic step modulus. Radius independence now covers all retained degrees on two disks that each admit the center with one unit of room.
[GaussianBarnesCanonicalFirstTaylorEvenReadback](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFirstTaylorEvenReadback.lean), [GaussianBarnesCanonicalTaylorFirstDerivativeAnchor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorFirstDerivativeAnchor.lean), [GaussianBarnesCanonicalTaylorAllOrderRadius](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorAllOrderRadius.lean), [GaussianBarnesCanonicalTaylorDerivativeBase](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorDerivativeBase.lean)

The two cofinal grid windows admit one common-centered original finite Taylor polynomial on a shared aperture. Their normalized mixed grid has a linear step error against twice the next original cofinal factorial name, with a disk and degree dependent gain and an explicit allowance at any independent target clock.
[GaussianBarnesCanonicalCofinalTaylorMixedGridRows](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorMixedGridRows.lean), [GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial.lean), [GaussianBarnesCanonicalCofinalTaylorMixedGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalCofinalTaylorMixedGridLimit.lean)

At every retained encoded order, the original adjacent cofinal factorial names form a regular named difference quotient with an explicit disk-only step modulus. Its limit is the original next factorial Taylor name at independently chosen observation clocks. Every admitted rational center has explicit arbitrarily small positive rational test steps after a positive integer refinement, and the target name transports back to the original chart. This verifies the rational-center successor derivative component of W3.
[GaussianBarnesCanonicalTaylorDerivativeSuccessor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorDerivativeSuccessor.lean), [GaussianBarnesCanonicalTaylorAllOrderDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorAllOrderDerivative.lean), [GaussianBarnesCanonicalTaylorDerivativeRefinement](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorDerivativeRefinement.lean)

The degree-zero fixed factorial Taylor name is the original literal finite product at the same cutoff. At arbitrary fixed cutoff, the original two signed grid windows use one common-centered stored Taylor polynomial and the mixed observation approaches twice the next fixed factorial name at a linear step rate and an independent target clock. The adjacent fixed-cutoff derivative theorem remains separate.
[GaussianBarnesCanonicalFixedTaylorDerivativeZero](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorDerivativeZero.lean), [GaussianBarnesCanonicalFiniteTaylorMixedGridRows](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorMixedGridRows.lean), [GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial.lean), [GaussianBarnesCanonicalFiniteTaylorMixedGridLimit](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorMixedGridLimit.lean)

The original named quotient of adjacent fixed factorial Taylor names converges to the next fixed factorial name at every positive encoded order, with one identical finite cutoff. Exact forward windows and a scheduled backward return rate justify the actual literal samples. The step modulus depends on disk and order and the observation clocks are independent.
[GaussianBarnesCanonicalFiniteTaylorEvenGridWindows](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorEvenGridWindows.lean), [GaussianBarnesCanonicalFiniteTaylorGridIncrementRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorGridIncrementRate.lean), [GaussianBarnesCanonicalFiniteTaylorNamedQuotient](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorNamedQuotient.lean), [GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorDerivativeSuccessor.lean)

The original cofinal factorial Taylor names have an explicit uniform input modulus at every encoded retained order for rational centers with independently chosen denominators. The corresponding regular Gaussian evaluator agrees with the rational names, respects equivalent input names, and is independent of the certified disk. The Lean derivations conclude these properties in iPRA with independent observation precisions.
[GaussianBarnesCanonicalTaylorDerivativeLocalContinuity](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalTaylorDerivativeLocalContinuity.lean), [GaussianBarnesCanonicalTaylorDerivativeUniformInput](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalTaylorDerivativeUniformInput.lean), [GaussianBarnesCanonicalNamedFactorialTaylor](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylor.lean), [GaussianBarnesCanonicalNamedFactorialTaylorBinding](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylorBinding.lean), [GaussianBarnesCanonicalNamedFactorialTaylorRadius](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylorRadius.lean)

At every admitted finite cutoff the original order-zero name is the literal product, and the original same-cutoff factorial Taylor names form a derivative chain at every encoded order. One disk-and-order step modulus controls the normalized quotient at independent observation precisions. Both the input and output Taylor buffers may be chosen independently as long as the corresponding orders are retained.
[GaussianBarnesCanonicalFiniteTaylorFirstPolynomial](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorFirstPolynomial.lean), [GaussianBarnesCanonicalFiniteTaylorFirstGridRate](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorFirstGridRate.lean), [GaussianBarnesCanonicalFiniteTaylorFirstDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorFirstDerivative.lean), [GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorDerivativeFirstSuccessor.lean), [GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalFiniteTaylorAllOrderDerivative.lean)

The degree-zero factorial Taylor evaluator is equivalent to the original named Barnes value. At every encoded order the actual named difference quotient under the certified small apart step hypothesis approaches the next named factorial Taylor value with independent observation clocks. The proof uses a common rational readback of the two endpoints and the step, with the readback clock accounting for the apartness certificate and the step threshold depending only on the disk, order, and requested precision.
[GaussianBarnesCanonicalNamedFactorialTaylorFrozen](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylorFrozen.lean), [GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints.lean), [GaussianBarnesCanonicalNamedFactorialTaylorZero](Lean/IPRADerivations/Analysis/Barnes/Names/GaussianBarnesCanonicalNamedFactorialTaylorZero.lean), [GaussianBarnesCanonicalNamedAllOrderDerivative](Lean/IPRADerivations/Analysis/Barnes/Taylor/Grids/GaussianBarnesCanonicalNamedAllOrderDerivative.lean)

At each encoded derivative order, two independently chosen total factor counts beyond one precision-dependent threshold give literal finite factorial derivative names with a uniform dyadic Cauchy bound. The threshold depends only on the disk radius, order, and precision. Different retaining buffers and equivalent rational encodings of the center are admitted.
[GaussianBarnesCanonicalFixedTaylorDerivativeCauchy](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalFixedTaylorDerivativeCauchy.lean)

One finite rational square grid covers the admitted disk. The primitive-recursive nearest entry identifies a certified local chart whose Taylor-ball error against the original Barnes evaluator has separate dyadic bounds in observation precision and degree.
[GaussianBarnesCanonicalWeightedTaylorBallCover](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBallCover.lean)

The exact finite harmonic numerator below a dyadic cutoff is at most one plus the dyadic index times the common unit. The literal Barnes head correction on a disk of radius R with N factors then has norm at most R squared times one plus this index, plus N times R.
[RationalHarmonicDyadicUpper](Lean/IPRADerivations/Analysis/Series/Harmonic/RationalHarmonicDyadicUpper.lean), [GaussianBarnesCanonicalDyadicHeadCorrection](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalDyadicHeadCorrection.lean)

Reading the actual stored coefficient, scaling by its factorial, and applying the original center scalar gives an independent-clock approximation to the cofinal derivative. A primitive-recursive clock on each retained order pays both schedule bounds.
[GaussianBarnesCanonicalWeightedTaylorBallCoefficient](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalWeightedTaylorBallCoefficient.lean)

A finite maximum of the retained coefficient clocks selects a single actual polynomial for the chosen grid chart. The closed iPRA certificate gives its exact center readback, geometric value error against the original Barnes evaluator, and independently observed dyadic error against the cofinal factorial Taylor name at every retained order.
[GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily](Lean/IPRADerivations/Analysis/Barnes/Taylor/Coefficients/GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily.lean), [GaussianBarnesCanonicalWeightedTaylorBallCoverCertificate](Lean/IPRADerivations/Analysis/Barnes/Taylor/GaussianBarnesCanonicalWeightedTaylorBallCoverCertificate.lean)

At every encoded integer m at least one, the original integer superfactorial sequence dominates the m-squared power of twice m at index four times m. A second closed bound uses base m and index four times m plus one. This establishes the arithmetic lower witness for the order and type argument.
[BarnesIntegerGrowth](Lean/IPRADerivations/Analysis/Barnes/BarnesIntegerGrowth.lean)

The original Barnes sampler at every encoded nonnegative integer n equals the constant superfactorial value G(n+1) at independent observation clocks. A quantifier-free induction controls the finite approximation error of the original recurrence and exact factorial factors.
[GaussianBarnesCanonicalIntegerRecurrence](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalIntegerRecurrence.lean), [GaussianBarnesCanonicalIntegerValues](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalIntegerValues.lean)

The exact integer value and the finite observation estimates supply a dyadic lower witness inside the prescribed disk. A primitive-recursive choice of the scale yields arbitrarily large quadratic type bounds for the actual canonical observations.
[GaussianBarnesCanonicalIntegerSampleLower](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalIntegerSampleLower.lean), [GaussianBarnesCanonicalDyadicLowerGrowth](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalDyadicLowerGrowth.lean)

The original kept powers and cofinal central exponential give a disk bound with base two and exponent proportional to the squared radius times its dyadic index plus one. The bound holds for the actual rational and regular Gaussian named evaluators at every observation precision.
[GaussianBarnesCanonicalDyadicHeadPower](Lean/IPRADerivations/Analysis/Barnes/HeadProducts/GaussianBarnesCanonicalDyadicHeadPower.lean), [GaussianBarnesCanonicalDyadicCentralBound](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalDyadicCentralBound.lean), [GaussianBarnesCanonicalDyadicCentralExponent](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalDyadicCentralExponent.lean), [GaussianBarnesCanonicalDyadicUpperGrowth](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalDyadicUpperGrowth.lean)

The named Barnes evaluator has an explicit upper threshold for every positive rational order gap on integer disks. A computed positive integer witness gives a quadratic lower exponent inside every sufficiently large disk. The separate dyadic witnesses exceed every prescribed quadratic type threshold. All estimates concern the actual canonical value or its named extension.
[BarnesUpperOrderThreshold](Lean/IPRADerivations/Analysis/Barnes/BarnesUpperOrderThreshold.lean), [BarnesDyadicRadius](Lean/IPRADerivations/Analysis/Barnes/BarnesDyadicRadius.lean), [GaussianBarnesCanonicalOrdinaryUpperGrowth](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalOrdinaryUpperGrowth.lean), [GaussianBarnesCanonicalOrdinaryLowerGrowth](Lean/IPRADerivations/Analysis/Barnes/GaussianBarnesCanonicalOrdinaryLowerGrowth.lean)

At every positive rational input the actual cofinal Euler log-Gamma sampler and certified reciprocal of the canonical Barnes sampler give one regular hyperfactorial name. The original product of that name with the canonical Barnes value equals the original exponentiated Gamma expression in iPRA.
[GaussianBarnesCanonicalHyperfactorial](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorial.lean)

The analytic hyperfactorial at one is the unit name. On positive rational charts the exponent agrees with its successor expansion using the original logarithmic Gamma recurrence. The original numerator at the successor is the product of the preceding numerator, the exponentiated log-Gamma name, and the original exp of z log z.
[GaussianBarnesCanonicalHyperfactorialNormalization](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialNormalization.lean), [GaussianBarnesCanonicalHyperfactorialExponentStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialExponentStep.lean), [GaussianBarnesCanonicalHyperfactorialPowerStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialPowerStep.lean)

The exact original degree-three factorial log row on the positive rational axis is positive. A shifted inverse-square telescope controls its original finite sum, with a positive first-row lower bound and an explicit decay bound for every full prefix.
[GaussianBarnesCanonicalThirdLogarithmRows](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmRows.lean), [GaussianBarnesCanonicalThirdLogarithmTail](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmTail.lean), [GaussianBarnesCanonicalThirdLogarithmSeries](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmSeries.lean)

The original Barnes and log-Gamma names satisfy the exact analytic hyperfactorial unit recurrence on every positive rational chart. Its value at every positive integer agrees with the exact finite hyperfactorial. The proofs use independent observation clocks and certified reciprocals.
[GaussianBarnesCanonicalHyperfactorialBarnesStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialBarnesStep.lean), [GaussianBarnesCanonicalHyperfactorialRecurrence](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialRecurrence.lean), [GaussianBarnesCanonicalHyperfactorialIntegers](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialIntegers.lean)

The actual named Barnes and log-Gamma samplers give the cleared hyperfactorial relation on certified right-half-plane inputs with Barnes apartness. On every positive rational input the proof constructs that certificate and identifies the named and rational implementations at independent observation precisions.
[GaussianBarnesCanonicalNamedHyperfactorial](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorial.lean), [GaussianBarnesCanonicalNamedHyperfactorialRational](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorialRational.lean)

The literal original cubic logarithm series on positive rationals has a primitive-recursive cutoff and a regular name at independent observation precisions. Every sample retains a positive first-row floor. A dyadic lower threshold on the input yields any requested upper precision.
[GaussianBarnesCanonicalThirdLogarithmCauchy](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmCauchy.lean), [GaussianBarnesCanonicalThirdLogarithmCofinal](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmCofinal.lean), [GaussianBarnesCanonicalThirdLogarithmOrder](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmOrder.lean)

Equivalent positive rational encodings give equivalent original hyperfactorial names at independent observation precisions. The proof preserves the original log-Gamma, Barnes, and reciprocal data up to their checked chart equivalences.
[GaussianBarnesCanonicalHyperfactorialProperness](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalHyperfactorialProperness.lean)

The checked second-logarithmic row increment uses the exact cubic derivative row and has error at most 3K⁴H²/(B²k³) for a shared positive margin. The retained interval error is at most 3K⁴H²/(B²N), and the full nonempty prefix error at most 6K⁴H²/B². The independent-clock cofinal cubic name agrees with the exact kept cubic rows plus the original factorial-scaled retained derivative name.
[GaussianBarnesCanonicalThirdDerivativeAlgebra](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdDerivativeAlgebra.lean), [GaussianBarnesCanonicalThirdDerivativeStep](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdDerivativeStep.lean), [GaussianBarnesCanonicalThirdDerivativePositiveMargin](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdDerivativePositiveMargin.lean), [GaussianBarnesCanonicalThirdDerivativeInterval](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdDerivativeInterval.lean), [GaussianBarnesCanonicalThirdLogarithmRetainedBinding](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdLogarithmRetainedBinding.lean)

The original negative quadratic prefactor coefficient, exact kept inverse-square rows, and cofinal second-row derivative form a regular second-logarithm expression. A common complete prefix compares its increment to the actual step times the original cubic name. The original native quotient has error at most 12K⁴ norm1(h)/B on the common positive physical margin. The identification of the second expression as a derivative of the full original logarithm is separate.
[GaussianBarnesCanonicalPositiveSecondLogarithm](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveSecondLogarithm.lean), [GaussianBarnesCanonicalThirdDerivativeCofinalBinding](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalThirdDerivativeCofinalBinding.lean)

For the actual regular names of H(z) and H(z+1), the original right-half-plane and Barnes apartness certificates at both inputs and the indicated pole-free Gamma presentation certificates give H(z+1) = H(z) exp(z Log(z)). The proof works at separately chosen certified observation radii and uses the original Barnes and Gamma recurrence samplers.
[GaussianBarnesCanonicalNamedHyperfactorialExponentStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorialExponentStep.lean), [GaussianBarnesCanonicalNamedHyperfactorialPowerStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorialPowerStep.lean), [GaussianBarnesCanonicalNamedHyperfactorialBarnesStep](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorialBarnesStep.lean), [GaussianBarnesCanonicalNamedHyperfactorialRecurrence](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalNamedHyperfactorialRecurrence.lean)

The weighted original rational logarithms of the kept bases are real at each observation and exponentiate to the original kept powers. Adding the original prefactor exponent, correction rows, and retained logarithm gives a regular name whose exponential is the original Barnes evaluator on every positive rational chart. The real-axis certificate for the remaining exponent components is separate.
[GaussianRationalFiniteSumAxis](Lean/IPRADerivations/Analysis/RationalArithmetic/FiniteSums/GaussianRationalFiniteSumAxis.lean), [GaussianBarnesCanonicalPositiveHeadLogarithm](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveHeadLogarithm.lean), [GaussianBarnesCanonicalPositiveHeadRealAxis](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveHeadRealAxis.lean), [GaussianBarnesCanonicalPositiveLogarithm](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveLogarithm.lean)

Actual signed grid observations with one-sided third-difference slack E obey a displacement bound 4N³E across a period, with exact constancy at zero slack. The modulo sampler supplies all periodic endpoint equalities. A common cubic Taylor comparison yields third-difference slack A+8E with exact leading force 6H³c₃, and the dyadic clock controls amplification.
[SignedGridStepBounds](Lean/IPRADerivations/Analysis/FiniteOperations/SignedGridStepBounds.lean), [PeriodicThirdDifferenceConstancy](Lean/IPRADerivations/Analysis/FiniteOperations/PeriodicThirdDifferenceConstancy.lean), [PeriodicThirdDifferenceModulo](Lean/IPRADerivations/Analysis/FiniteOperations/PeriodicThirdDifferenceModulo.lean), [SignedCubicTaylorGrid](Lean/IPRADerivations/Analysis/FiniteOperations/SignedCubicTaylorGrid.lean)

For every positive rational half-grid z=A/(2B), the original four-factor Barnes product and G(2z) acquire the same certified Gamma multiplier after the exponential normalization. The actual cleared quotient products at z and z+1/2 are cross-equivalent. This proves the half-period step of the multiplication argument, with the asymptotic constant determination still separate.
[GaussianBarnesCanonicalDuplicationShift](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalDuplicationShift.lean), [GaussianBarnesCanonicalDuplicationNormalizerCoefficients](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalDuplicationNormalizerCoefficients.lean), [GaussianBarnesCanonicalDuplicationNormalizer](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalDuplicationNormalizer.lean), [GaussianBarnesCanonicalDuplicationGamma](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalDuplicationGamma.lean), [GaussianBarnesCanonicalDuplicationPeriodicity](Lean/IPRADerivations/Analysis/Barnes/FunctionalEquations/GaussianBarnesCanonicalDuplicationPeriodicity.lean)

The original prefactor derivative, exact kept first rows, finite correction slope, and cofinal first derivative name are tied together by exact rational and named identities. The native first-expression divided quotient agrees with the actual second-logarithm expression to error at most 4K³ norm1(h)/B on the common positive margin. The calculus link from the full original logarithm to the first expression is separate.
[GaussianBarnesCanonicalPositiveFirstDerivativeRow](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveFirstDerivativeRow.lean), [GaussianBarnesCanonicalPositiveFirstLogarithm](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveFirstLogarithm.lean), [GaussianBarnesCanonicalPositiveFirstLogarithmKept](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveFirstLogarithmKept.lean), [GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor.lean), [GaussianBarnesCanonicalPositiveSecondDerivativeInterval](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveSecondDerivativeInterval.lean), [GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveSecondDerivativeSeriesBinding.lean), [GaussianBarnesCanonicalPositiveSecondDerivativeBinding](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveSecondDerivativeBinding.lean)

The actual rounding of any original Gaussian observation transfers its metric comparison to the signed grid with one lattice unit of error. The original modulo sampler handles all wrapped stencil nodes. Reading the periodic bound back to real projections costs two units, and a verified dyadic clock pays both rounding errors and the full third-difference amplification.
[GaussianSignedObservationGrid](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianSignedObservationGrid.lean), [GaussianSignedObservationReadback](Lean/IPRADerivations/Analysis/FiniteOperations/GaussianSignedObservationReadback.lean)

Every actual sample of the positive rational Barnes logarithm is real, and its exponential is the original Barnes value. Equal rational center presentations and separately certified radii give equivalent real names. For a certified real small step the original relative evaluator is exactly equivalent to the difference of the two full real logarithms.
[GaussianBarnesCanonicalLogarithmRealPrefix](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogarithmRealPrefix.lean), [GaussianBarnesCanonicalLogarithmRealTail](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalLogarithmRealTail.lean), [GaussianBarnesCanonicalPositiveLogarithmRealAxis](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveLogarithmRealAxis.lean), [GaussianBarnesCanonicalHeadRelativeRealAxis](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalHeadRelativeRealAxis.lean), [GaussianBarnesCanonicalRelativeLogarithmRealAxis](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalRelativeLogarithmRealAxis.lean), [GaussianBarnesCanonicalPositiveLogarithmIncrement](Lean/IPRADerivations/Analysis/Barnes/Logarithms/GaussianBarnesCanonicalPositiveLogarithmIncrement.lean)
