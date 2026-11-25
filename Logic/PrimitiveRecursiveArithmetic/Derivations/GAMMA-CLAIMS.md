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
[GaussianGammaEulerShift](Lean/IPRADerivations/Analysis/GaussianGammaEulerShift.lean)
proves the corresponding shift for the original finite Euler names
with the actual `exp(−log N)` factor.
[GaussianGammaEulerShiftLimit](Lean/IPRADerivations/Analysis/GaussianGammaEulerShiftLimit.lean)
computes the correction and its exact error under the mesh-log inverse
identity. [GaussianGammaFunctionalEquation](Lean/IPRADerivations/Analysis/GaussianGammaFunctionalEquation.lean)
proves the original C7 shift under that identity for all positive cutoffs.
[RationalReciprocalPowerTail](Lean/IPRADerivations/Analysis/RationalReciprocalPowerTail.lean)
proves the C17 sharp finite tail for the actual reciprocal-power sum.
The bound retains the endpoint potential for every numerical length,
with exponent `m≥2` and starting index `N≥1`.
[RationalReciprocalPowerName](Lean/IPRADerivations/Analysis/RationalReciprocalPowerName.lean)
gives the C17 cofinal zeta sampler and the shifted tail as regular names.
Each raw tail observation satisfies the exact sharp bound and is nonnegative.
The original finite reciprocal-power prefix plus this tail reconstructs the
same zeta name at independent observation precisions.
[GaussianGammaFiniteDegreeRearrangement](Lean/IPRADerivations/Analysis/GaussianGammaFiniteDegreeRearrangement.lean)
proves the finite C16 degree rearrangement for the actual normalized tail.
Its returned PR program computes both equal rectangle values, and the
original `R²/N` bound applies to the value.
[GaussianGammaReciprocalDegreeCells](Lean/IPRADerivations/Analysis/GaussianGammaReciprocalDegreeCells.lean)
separates each literal degree column into its signed monomial and the
actual rational reciprocal-power partial sum.
[GaussianGammaDegreeTail](Lean/IPRADerivations/Analysis/GaussianGammaDegreeTail.lean)
proves the exact C18 error `R²/(N·2^(L+1))` between finite rectangles
of degrees `L+2` and `L+J+2`, including the original `N=2R` choice.
[GaussianGammaFixedDegreeHorizon](Lean/IPRADerivations/Analysis/GaussianGammaFixedDegreeHorizon.lean)
proves the exact change with factor horizon at a fixed degree and
constructs its regular cofinal name with the original factor clock.
[GaussianGammaCofinalDegreeTail](Lean/IPRADerivations/Analysis/GaussianGammaCofinalDegreeTail.lean)
proves the same C18 error against the original cofinal tail at independent
precisions, with the two requested observation errors.
[GaussianGammaZetaDegreeName](Lean/IPRADerivations/Analysis/GaussianGammaZetaDegreeName.lean)
identifies the original fixed-degree tail with the actual C17 zeta-tail
polynomial, retaining the exact C18 bound.
[GaussianGammaZetaTailSeries](Lean/IPRADerivations/Analysis/GaussianGammaZetaTailSeries.lean)
uses the cofinal degree `L_p=p+R²` to construct the actual C16 zeta series
and proves its equivalence with the original tail at independent
precisions, including the source cutoff `N=2R`.
[GaussianFiniteExponentialCoefficientMajorant](Lean/IPRADerivations/Analysis/GaussianFiniteExponentialCoefficientMajorant.lean)
proves the finite weighted coefficient bound for the original polynomial
exponential. [GaussianWeightedPolynomialTail](Lean/IPRADerivations/Analysis/GaussianWeightedPolynomialTail.lean)
proves the finite C19 geometric tail on the rescaled half disk. The
Comparison of coefficient names across radii and cofinal analyticity remain.
[GaussianGammaZetaCoefficientPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaZetaCoefficientPolynomial.lean)
constructs the actual degree buffer and binds its Horner value to the
original C16 polynomial at its original clock.
[GaussianGammaZetaCoefficientNorm](Lean/IPRADerivations/Analysis/GaussianGammaZetaCoefficientNorm.lean)
derives the original sampled weighted coefficient bound
`R^m/(m(m−1)N^(m−1))` for each `m≥2`.
[GaussianGammaZetaWeightedNorm](Lean/IPRADerivations/Analysis/GaussianGammaZetaWeightedNorm.lean)
sums the original stored coefficients to prove the full finite tail
mass `R²/N` for every cutoff and observation precision.
[GaussianGammaLinearCoefficient](Lean/IPRADerivations/Analysis/GaussianGammaLinearCoefficient.lean)
checks the original sampled Euler-linear monomial and its mass
`R(N+1)`.
[GaussianGammaExponentCoefficientPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaExponentCoefficientPolynomial.lean)
combines the original sampled exponent coefficients and bounds the
weighted mass of their finite exponential at cutoff `2R`.
[GaussianGammaEulerFactorPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaEulerFactorPolynomial.lean)
evaluates the actual stored two-entry Euler factor.
[GaussianGammaEulerHeadPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaEulerHeadPolynomial.lean)
builds the actual head by coefficient convolution and proves weighted
mass at most `R(1+R)^N`.
[GaussianGammaFiniteCoefficientPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaFiniteCoefficientPolynomial.lean)
evaluates the full finite product of the original head and sampled
finite exponential. Its exact weighted coefficient majorant is the
original `M_R`. A prefix through degree `d` has discarded-tail
error at most `M_(2R)/2^(d+1)` on the radius-`R` disk.
[GaussianGammaSynchronousExponentName](Lean/IPRADerivations/Analysis/GaussianGammaSynchronousExponentName.lean)
proves that a regular sampler evaluates the same sampled exponent
coefficient buffer with clocks determined solely by radius and precision.
[GaussianGammaSynchronousExponentCompatibility](Lean/IPRADerivations/Analysis/GaussianGammaSynchronousExponentCompatibility.lean)
identifies that sampler with the original C7 exponent at independent
precisions on the original disk.
[GaussianBoundedConstantProductName](Lean/IPRADerivations/Analysis/GaussianBoundedConstantProductName.lean)
then provides a regular multiplication clock depending only on the
numerical bound for the constant. This lets the finite coefficient
sampler multiply by the original head with an argument-independent clock.
[GaussianGammaCofinalCoefficientName](Lean/IPRADerivations/Analysis/GaussianGammaCofinalCoefficientName.lean)
binds the resulting observations to the original computed coefficient
polynomials and the original C7 name. All three coefficient clocks depend
solely on radius and precision.
[GaussianGammaOriginalC19Prefix](Lean/IPRADerivations/Analysis/GaussianGammaOriginalC19Prefix.lean)
compares the computed degree prefix directly to the original C7 name
with the exact C19 degree bound and independent observation errors.
[GaussianGammaPolynomialConstantLinear](Lean/IPRADerivations/Analysis/GaussianGammaPolynomialConstantLinear.lean)
checks the actual constant and linear coefficients of the cofinal
polynomial as zero and one.
[GaussianPolynomialLinearFactorCoefficients](Lean/IPRADerivations/Analysis/GaussianPolynomialLinearFactorCoefficients.lean)
checks the original quadratic coefficient under a linear factor.
[GaussianPolynomialExponentialLinear](Lean/IPRADerivations/Analysis/GaussianPolynomialExponentialLinear.lean)
proves preservation of the linear coefficient by the actual finite
exponential when the input constant coefficient is zero.
[GaussianGammaEulerHeadQuadratic](Lean/IPRADerivations/Analysis/GaussianGammaEulerHeadQuadratic.lean)
identifies the quadratic entry of the Euler head with the harmonic sum.
[GaussianGammaPolynomialQuadratic](Lean/IPRADerivations/Analysis/GaussianGammaPolynomialQuadratic.lean)
identifies the exact cofinal quadratic coefficient name with the
original Euler–Mascheroni name.
[GaussianGammaFiniteQuadraticExpansion](Lean/IPRADerivations/Analysis/GaussianGammaFiniteQuadraticExpansion.lean)
bounds the remainder of the unchanged finite polynomial by a cubic
in the shrinking input radius.
[GaussianGammaQuadraticSampler](Lean/IPRADerivations/Analysis/GaussianGammaQuadraticSampler.lean)
extends that bound to the original reciprocal Gamma observations. The
independent Euler–Mascheroni observation error retains its quadratic
input-radius factor.
[GaussianGammaExponentCoefficientStability](Lean/IPRADerivations/Analysis/GaussianGammaExponentCoefficientStability.lean)
proves fixed exponent-coefficient equality across degree horizons
at the same sample precision and Euler cutoff.
[GaussianPolynomialExponentialCapStability](Lean/IPRADerivations/Analysis/GaussianPolynomialExponentialCapStability.lean)
checks that each original finite exponential coefficient is unchanged
across caps at least its exponent for zero constant input.
[GaussianPolynomialLowJetProduct](Lean/IPRADerivations/Analysis/GaussianPolynomialLowJetProduct.lean)
transfers coefficient agreement through the actual product of buffers
with different stored degrees.
[GaussianGammaPowerHorizonCoherence](Lean/IPRADerivations/Analysis/GaussianGammaPowerHorizonCoherence.lean),
[GaussianGammaExponentialHorizonCoherence](Lean/IPRADerivations/Analysis/GaussianGammaExponentialHorizonCoherence.lean),
and [GaussianGammaFiniteCoefficientStability](Lean/IPRADerivations/Analysis/GaussianGammaFiniteCoefficientStability.lean)
reduce every literal cofinal coefficient observation to the actual fixed
coefficient at its degree-sized truncations and original precision clock.
[GaussianPolynomialPowerNormVariation](Lean/IPRADerivations/Analysis/GaussianPolynomialPowerNormVariation.lean)
checks the perturbation bound for the actual finite power cursor.
[GaussianPolynomialExponentialCoefficientVariation](Lean/IPRADerivations/Analysis/GaussianPolynomialExponentialCoefficientVariation.lean)
preserves each factorial weight in the original finite exponential
coefficient error.
[GaussianGammaInputPrecisionNorm](Lean/IPRADerivations/Analysis/GaussianGammaInputPrecisionNorm.lean)
proves the actual input coefficient buffer error across precisions.
[GaussianGammaInputStaticNorm](Lean/IPRADerivations/Analysis/GaussianGammaInputStaticNorm.lean)
gives its canonical fixed-degree norm envelope.
[GaussianGammaFixedCoefficientVariation](Lean/IPRADerivations/Analysis/GaussianGammaFixedCoefficientVariation.lean)
derives a computed precision modulus for the full actual fixed
coefficient for every degree.
[GaussianGammaHigherCoefficientName](Lean/IPRADerivations/Analysis/GaussianGammaHigherCoefficientName.lean)
constructs a regular name at every degree from the unchanged cofinal
coefficient sampler at radius `e+1`.
[GaussianGammaRadiusCoefficientName](Lean/IPRADerivations/Analysis/GaussianGammaRadiusCoefficientName.lean)
keeps the radius as an actual input.
[GaussianGammaAllDegreeCoefficientStability](Lean/IPRADerivations/Analysis/GaussianGammaAllDegreeCoefficientStability.lean)
and [GaussianGammaAllDegreeCoefficientVariation](Lean/IPRADerivations/Analysis/GaussianGammaAllDegreeCoefficientVariation.lean)
remove the head-degree restriction by exact product coefficient
preservation under padding. The unchanged name is regular for every
internal degree at any fixed positive radius.
[GaussianLagrangeInterpolation](Lean/IPRADerivations/Analysis/GaussianLagrangeInterpolation.lean)
recovers finite original coefficients from actual natural-grid observations.
[GaussianLagrangeCoefficientSensitivity](Lean/IPRADerivations/Analysis/GaussianLagrangeCoefficientSensitivity.lean)
computes the error gain of the original inverse row.
[GaussianShrinkingPolynomialTail](Lean/IPRADerivations/Analysis/GaussianShrinkingPolynomialTail.lean)
retains the exact power of the shrinking radius in the finite tail bound.
[GaussianShrinkingGridValueRecovery](Lean/IPRADerivations/Analysis/GaussianShrinkingGridValueRecovery.lean)
uses the original full polynomial values on the shrinking grid. The
checked low-prefix program and exact rational dilation give a bound
for the difference of the actual coefficients.
[GaussianGammaUnitCoefficientMass](Lean/IPRADerivations/Analysis/GaussianGammaUnitCoefficientMass.lean)
bounds the total ordinary coefficient norm of each original polynomial.
[GaussianGammaCoefficientRadiusIndependence](Lean/IPRADerivations/Analysis/GaussianGammaCoefficientRadiusIndependence.lean)
proves that the actual coefficient names agree at every pair of positive
radii, including the original canonical radius.
[GaussianGammaOriginalPrefixName](Lean/IPRADerivations/Analysis/GaussianGammaOriginalPrefixName.lean)
regularizes the unchanged original finite prefix and proves its literal
C19 approximation bound with independent precisions.
[GaussianGammaCanonicalPrefixName](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalPrefixName.lean)
supplies the regular finite evaluator of the original canonical names.
[GaussianGammaCanonicalPrefixTaylor](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalPrefixTaylor.lean) compares the actual original finite C19 polynomial
to the finite sum of actual canonical coefficient observations at any
internal order. Its remainder retains the full power of the shrinking
input radius, with separate finite-cutoff and coefficient-query errors.
[GaussianGammaCanonicalTaylorSampler](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalTaylorSampler.lean) removes the auxiliary finite-polynomial query from the bound
for the original reciprocal Gamma sampler. The resulting error is the
shrinking tail plus one output observation error and the coefficient
observation error multiplied by the number of retained terms.
[GaussianGammaDeflatedPrefixTaylor](Lean/IPRADerivations/Analysis/GaussianGammaDeflatedPrefixTaylor.lean) factors the exact canonical prefix by its argument and
checks the value one at zero for the deflated prefix.
[GaussianGammaShiftedDeflatedPolynomial](Lean/IPRADerivations/Analysis/GaussianGammaShiftedDeflatedPolynomial.lean) factors the original full Euler polynomial and compares
its deflated value with the shifted reciprocal Gamma at independent
precisions on the certified nonzero native guard.
[GaussianGammaShiftedDeflatedName](Lean/IPRADerivations/Analysis/GaussianGammaShiftedDeflatedName.lean) packages this comparison as a regular name through a
computed retiming and proves equivalence to the original shifted name.
[GaussianGammaShiftedDeflatedZero](Lean/IPRADerivations/Analysis/GaussianGammaShiftedDeflatedZero.lean) evaluates the same deflated polynomial and shifted reciprocal
name at the native zero input.
[GaussianGammaShiftedDeflatedIdentification](Lean/IPRADerivations/Analysis/GaussianGammaShiftedDeflatedIdentification.lean) proves the same original name equivalence over the full
native source, including zero. [GaussianGammaDeflatedFiniteTaylor](Lean/IPRADerivations/Analysis/GaussianGammaDeflatedFiniteTaylor.lean) proves the true deflated
polynomial remainder with the full power of the shrinking radius.
[GaussianGammaShiftedTaylorSampler](Lean/IPRADerivations/Analysis/GaussianGammaShiftedTaylorSampler.lean) transfers that remainder to the original shifted reciprocal
Gamma observation at every internal order. It retains the original
canonical coefficient observations and their independent clock, and
covers zero increment.
[GaussianGammaPrefixCompatibility](Lean/IPRADerivations/Analysis/GaussianGammaPrefixCompatibility.lean)
identifies the two prefix names and proves the literal C19 rate with
these canonical coefficients on the original encoded disk.
[GaussianRobinOddLogarithm](Lean/IPRADerivations/Analysis/GaussianRobinOddLogarithm.lean)
and [GaussianRobinLogarithmParity](Lean/IPRADerivations/Analysis/GaussianRobinLogarithmParity.lean)
identify the original finite Robin artanh component with the difference of
the two original local logarithm polynomials evaluated at opposite rational
inputs. [GaussianRobinOddLogarithmName](Lean/IPRADerivations/Analysis/GaussianRobinOddLogarithmName.lean)
constructs a regular sampler from the stored odd series and proves
its equivalence with the actual difference of the two regular local
logarithm names.
[GaussianRobinOddExponential](Lean/IPRADerivations/Analysis/GaussianRobinOddExponential.lean)
identifies the actual exponential of that odd name with the constant
`(b+a)/(b−a)` on the half disk.
[GaussianRobinLogRangeReduction](Lean/IPRADerivations/Analysis/GaussianRobinLogRangeReduction.lean)
identifies the actual exponentials of the original two binary components
as `2` and `a/Bt(a,b)`.
[GaussianRobinLowerDecomposition](Lean/IPRADerivations/Analysis/GaussianRobinLowerDecomposition.lean)
proves the exact decomposition of the original stored lower endpoint at
every numerical cutoff into the two actual odd sums and the binary exponent.
[GaussianRobinMeshLogDecomposition](Lean/IPRADerivations/Analysis/GaussianRobinMeshLogDecomposition.lean)
identifies their named weighted sum with the original mesh logarithm
at independent observation precisions.
[GaussianNamedNaturalScale](Lean/IPRADerivations/Analysis/GaussianNamedNaturalScale.lean)
and [GaussianNaturalScaleProductName](Lean/IPRADerivations/Analysis/GaussianNaturalScaleProductName.lean)
identify the actual retimed scaling with named multiplication.
[GaussianRobinIntegerExponential](Lean/IPRADerivations/Analysis/GaussianRobinIntegerExponential.lean)
proves the exponential law for every numerical binary exponent by
quantifier-free induction on a finite error comparison.
[GaussianMeshLogSign](Lean/IPRADerivations/Analysis/GaussianMeshLogSign.lean)
checks the exact named negation and reciprocal transport.
[GaussianRobinMeshExponential](Lean/IPRADerivations/Analysis/GaussianRobinMeshExponential.lean)
combines the original range-reduced components and proves
`exp(log N)=N` and `exp(−log N)=1/N` for the original mesh name.
This proves C20 with its original disk conditions.
[GaussianGammaNormalization](Lean/IPRADerivations/Analysis/GaussianGammaNormalization.lean)
uses the original Euler head at one and the finite convergence rate
to prove `P(1)=1` and `Γ(1)=1` once the mesh identity is supplied.
[GaussianGammaShift](Lean/IPRADerivations/Analysis/GaussianGammaShift.lean)
uses the reciprocal shift and checked inverse product to prove
`Γ(z+1)=zΓ(z)` on the recorded original two pole-free domains.
[GaussianGammaShiftTrajectory](Lean/IPRADerivations/Analysis/GaussianGammaShiftTrajectory.lean)
constructs the actual native successor trajectory, proves its disk at
every numerical stage, and identifies its encoded coordinate values.
[GaussianGammaFactorialValues](Lean/IPRADerivations/Analysis/GaussianGammaFactorialValues.lean)
then proves the original C21 factorial identity for all internal indices.
[GaussianGammaRepeatedShift](Lean/IPRADerivations/Analysis/GaussianGammaRepeatedShift.lean)
proves C22 for the original reciprocal Gamma name and the actual rising
product, including zero factors.
[GaussianGammaRisingFactorial](Lean/IPRADerivations/Analysis/GaussianGammaRisingFactorial.lean)
proves V8 for the original Gamma names wherever both endpoints have
certified pole margins. Every internal index is allowed, including zero.
The observation program returns the actual rising product and the two
sides of the identity at independent precisions.
[GaussianGammaBinomialCleared](Lean/IPRADerivations/Analysis/GaussianGammaBinomialCleared.lean)
proves the entire cleared V9 identity using the actual generalized
binomial polynomial, including its values at apparent cancelled poles.
[GaussianGammaBinomialQuotient](Lean/IPRADerivations/Analysis/GaussianGammaBinomialQuotient.lean)
identifies the actual formal Gamma quotient with that polynomial
where the two original Gamma endpoint guards hold. Both proofs
allow every internal index, including zero.
[GaussianGammaLocalPoleGuards](Lean/IPRADerivations/Analysis/GaussianGammaLocalPoleGuards.lean)
derives the original punctured-disk domain for C24 and the separated
terminal argument `1+h/B`.
[GaussianGammaPoleFiniteFactors](Lean/IPRADerivations/Analysis/GaussianGammaPoleFiniteFactors.lean)
identifies the actual reversed rising factors with the signed factorial
times the finite normalized correction product.
[GaussianGammaPoleMultiplier](Lean/IPRADerivations/Analysis/GaussianGammaPoleMultiplier.lean)
checks the inverse step and the actual finite product of inverse factors.
[GaussianGammaLocalPoleFormula](Lean/IPRADerivations/Analysis/GaussianGammaLocalPoleFormula.lean)
proves C24 and its cleared form for the original Gamma names at every
encoded rational increment in the punctured unit disk. It computes
both margins from the integer squared norm of the increment.
[GaussianGammaPoleFactorContinuity](Lean/IPRADerivations/Analysis/GaussianGammaPoleFactorContinuity.lean)
proves the explicit rational error of the original finite normalized
factor product near the pole.
[GaussianGammaPoleReciprocalFactor](Lean/IPRADerivations/Analysis/GaussianGammaPoleReciprocalFactor.lean)
proves the original C23 factorization throughout the encoded closed
unit disk.
[GaussianGammaPoleQuotientCenter](Lean/IPRADerivations/Analysis/GaussianGammaPoleQuotientCenter.lean)
and [GaussianGammaPoleCenterValue](Lean/IPRADerivations/Analysis/GaussianGammaPoleCenterValue.lean)
check the exact center values of the reciprocal quotient and regularized
Gamma name against the signed factorial and signed inverse factorial.
[GaussianGammaPoleInverseContinuity](Lean/IPRADerivations/Analysis/GaussianGammaPoleInverseContinuity.lean)
proves the corresponding actual inverse-factor perturbation bound on
the half disk.
[GaussianGammaTerminalContinuity](Lean/IPRADerivations/Analysis/GaussianGammaTerminalContinuity.lean)
proves the fixed half-disk certificate for the actual terminal argument
and transfers an independent C7 rate at one to the original Gamma name.
[GaussianGammaPoleProductRate](Lean/IPRADerivations/Analysis/GaussianGammaPoleProductRate.lean),
[GaussianGammaPoleLimitTransport](Lean/IPRADerivations/Analysis/GaussianGammaPoleLimitTransport.lean),
and [GaussianGammaPoleLimitModulus](Lean/IPRADerivations/Analysis/GaussianGammaPoleLimitModulus.lean)
derive both local product observations at a common computed precision
from a specified terminal C7 rate.
[GaussianGammaPoleDifferenceQuotient](Lean/IPRADerivations/Analysis/GaussianGammaPoleDifferenceQuotient.lean)
binds the factored quotient to the actual division on the punctured disk.
[GaussianGammaPoleLimits](Lean/IPRADerivations/Analysis/GaussianGammaPoleLimits.lean)
derives the terminal rate and proves the C23 and C25 dyadic limits of
the actual divided reciprocal and the original cleared Gamma on encoded
rational increments. The bound holds for every later observation.
[GaussianRationalConjugation](Lean/IPRADerivations/Analysis/GaussianRationalConjugation.lean)
proves exact conjugation for rational code, metric and scalar Taylor sums.
[GaussianGammaFiniteConjugation](Lean/IPRADerivations/Analysis/GaussianGammaFiniteConjugation.lean)
proves covariance of the original finite head, local factors and literal
prefix for C26.
[GaussianNameConjugation](Lean/IPRADerivations/Analysis/GaussianNameConjugation.lean)
transports conjugation through the actual regular-name operations.
[GaussianGammaNameConjugation](Lean/IPRADerivations/Analysis/GaussianGammaNameConjugation.lean)
proves conjugation of the original C7 reciprocal via the literal C11
cofinal Weierstrass sampler, including at every zero of the original head.
[GaussianGammaInverseConjugation](Lean/IPRADerivations/Analysis/GaussianGammaInverseConjugation.lean)
proves conjugation for the same pole-free Gamma inverse.
[GaussianGammaRealValues](Lean/IPRADerivations/Analysis/GaussianGammaRealValues.lean)
constructs actual rational regular names for the real values of both
original Gamma names at encoded real rational inputs.
[GaussianGammaFiniteValueProperness](Lean/IPRADerivations/Analysis/GaussianGammaFiniteValueProperness.lean)
and [GaussianGammaInputProperness](Lean/IPRADerivations/Analysis/GaussianGammaInputProperness.lean)
prove that equality of the native coordinate values at a fixed denominator
is respected by the original reciprocal and pole-free Gamma names.
[GaussianGammaEulerHeadContinuity](Lean/IPRADerivations/Analysis/GaussianGammaEulerHeadContinuity.lean)
proves the actual finite head modulus on each fixed-radius disk for
two encodings with the same denominator.
[GaussianGammaEncodingRescaling](Lean/IPRADerivations/Analysis/GaussianGammaEncodingRescaling.lean)
proves C7 agreement under positive rescaling of both numerator and
denominator, including all positive encodings of one.
[GaussianGammaLogExponentContinuity](Lean/IPRADerivations/Analysis/GaussianGammaLogExponentContinuity.lean)
and [GaussianGammaEulerContinuityReference](Lean/IPRADerivations/Analysis/GaussianGammaEulerContinuityReference.lean)
derive the original C7 comparison with a finite shared reference and
bound the reference variation in the input.
[GaussianGammaInputContinuity](Lean/IPRADerivations/Analysis/GaussianGammaInputContinuity.lean)
derives the uniform input modulus for the original C7 name from this
reference. It preserves independent observation errors.
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

### Checked Euler quadrature

[GaussianEulerExponentCompactBounds](Lean/IPRADerivations/Analysis/GaussianEulerExponentCompactBounds.lean)
bounds the original exponent on the compact interval and follows both
program clocks. [GaussianEulerCompactModulus](Lean/IPRADerivations/Analysis/GaussianEulerCompactModulus.lean)
derives the local sampled modulus for the unchanged Euler integrand from
the positive rational time interval and the native bound on the complex
parameter. [GaussianGammaEulerCompactQuadrature](Lean/IPRADerivations/Analysis/GaussianGammaEulerCompactQuadrature.lean)
supplies the actual fixed-interval quadrature name at the prescribed
Gamma endpoints. Its checked modulus uses a larger mesh factor than the
paper’s proposed derivative bound.

[GaussianEulerDecayQuadraturePrecision](Lean/IPRADerivations/Analysis/GaussianEulerDecayQuadraturePrecision.lean)
proves the decay endpoint estimate with independent observation
precisions and the exact geometric mesh term.
[GaussianEulerDecayCompactAntiderivative](Lean/IPRADerivations/Analysis/GaussianEulerDecayCompactAntiderivative.lean)
identifies the resulting compact decay name with the original
difference of endpoint decay names.
[GaussianSignedRealExponentialOrder](Lean/IPRADerivations/Analysis/GaussianSignedRealExponentialOrder.lean)
proves signed real-axis order for the unchanged named exponential.
[GaussianCompactRiemannSplit](Lean/IPRADerivations/Analysis/GaussianCompactRiemannSplit.lean)
checks the exact finite split of the actual affine grid at a common step.
[GaussianCompactRiemannAdditivity](Lean/IPRADerivations/Analysis/GaussianCompactRiemannAdditivity.lean)
compares the actual shared-step observations via their zero-distance
rate across distinct rational time encodings.
[GaussianPositiveRationalLogarithmSign](Lean/IPRADerivations/Analysis/GaussianPositiveRationalLogarithmSign.lean)
proves the sign of the original logarithm up to observation error.
[GaussianExponentialRealPartMajorant](Lean/IPRADerivations/Analysis/GaussianExponentialRealPartMajorant.lean)
bounds the original complex exponential squared modulus from its actual
real part.
[GaussianEulerDecayOrder](Lean/IPRADerivations/Analysis/GaussianEulerDecayOrder.lean)
proves order in the original rational time and binds the actual
nonnegative representative.
[GaussianCompactNamedAdditivity](Lean/IPRADerivations/Analysis/GaussianCompactNamedAdditivity.lean)
proves addition for the original regular compact names, and
[GaussianEulerCompactAdditivity](Lean/IPRADerivations/Analysis/GaussianEulerCompactAdditivity.lean)
instantiates it for the unchanged Euler evaluator on positive intervals.
[GaussianEulerHalfDecayQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerHalfDecayQuadrature.lean)
checks the actual half-argument grid transformation.
[GaussianEulerDecayEndpointBound](Lean/IPRADerivations/Analysis/GaussianEulerDecayEndpointBound.lean)
controls the endpoint difference using the left endpoint observation, and
[GaussianEulerHalfDecayTailBound](Lean/IPRADerivations/Analysis/GaussianEulerHalfDecayTailBound.lean)
checks the finite upper-cutoff bound for the half-decay kernel.
[GaussianHarmonicLogarithmName](Lean/IPRADerivations/Analysis/GaussianHarmonicLogarithmName.lean)
supplies an exact-order representative of the original logarithm.
[GaussianHarmonicIntegerExponential](Lean/IPRADerivations/Analysis/GaussianHarmonicIntegerExponential.lean)
identifies the actual exponential of its natural multiple with the
exact rational power.
[GaussianEulerUpperPowerCoefficients](Lean/IPRADerivations/Analysis/GaussianEulerUpperPowerCoefficients.lean)
checks the actual doubled real multiplier bound and the nonnegative
harmonic inputs for time at least one.
[GaussianEulerUpperPowerBound](Lean/IPRADerivations/Analysis/GaussianEulerUpperPowerBound.lean)
proves the bound `t^R+2^-p` at each original power sample.
[GaussianEulerHalfDecayProduct](Lean/IPRADerivations/Analysis/GaussianEulerHalfDecayProduct.lean)
identifies the original integrand with its power and the two half-decay
factors. [GaussianEulerWeightedHalfDecay](Lean/IPRADerivations/Analysis/GaussianEulerWeightedHalfDecay.lean)
checks the factorial majorant of the first product with explicit slack.
[GaussianEulerHalfDecayReference](Lean/IPRADerivations/Analysis/GaussianEulerHalfDecayReference.lean)
gives the nonnegative scalar representative of the second factor.
[GaussianEulerUpperTailPointwise](Lean/IPRADerivations/Analysis/GaussianEulerUpperTailPointwise.lean)
bounds every original integrand observation at time at least one by
`2^R R!(H_q+2^-q)+2^-p`, where `H_q` is the independent nonnegative
half-decay observation.
[GaussianCompactMeshIndependence](Lean/IPRADerivations/Analysis/GaussianCompactMeshIndependence.lean),
[GaussianCompactIntervalRescaling](Lean/IPRADerivations/Analysis/GaussianCompactIntervalRescaling.lean)
and [GaussianEulerCompactAlignment](Lean/IPRADerivations/Analysis/GaussianEulerCompactAlignment.lean)
identify the original compact Euler names across different legitimate
mesh bounds and rational encodings of the same interval.
[GaussianGammaCompactCutoffGeometry](Lean/IPRADerivations/Analysis/GaussianGammaCompactCutoffGeometry.lean)
and [GaussianGammaCompactCutoffAlignment](Lean/IPRADerivations/Analysis/GaussianGammaCompactCutoffAlignment.lean)
relate the actual cutoff denominators and align the earlier Euler
quadrature name with the corresponding interval at the later cutoff.
[GaussianGammaCompactCutoffSplit](Lean/IPRADerivations/Analysis/GaussianGammaCompactCutoffSplit.lean)
checks the resulting three-piece decomposition of the original
later name, including coincident cutoffs.
[GaussianCompactScalarMajorant](Lean/IPRADerivations/Analysis/GaussianCompactScalarMajorant.lean)
sums the pointwise scalar majorant on the original grid and passes an
independent row comparison through the actual quadrature weight.
[GaussianEulerCompactUpperTail](Lean/IPRADerivations/Analysis/GaussianEulerCompactUpperTail.lean)
proves the upper-cutoff norm bound for the original finite Euler
quadrature using the scaled half-decay kernel and explicit mesh and
observation errors.
[GaussianEulerHalfDecayLeftNorm](Lean/IPRADerivations/Analysis/GaussianEulerHalfDecayLeftNorm.lean)
retains a bound on the actual left decay observation at arbitrary
rational time. [GaussianEulerUpperTailLeftNorm](Lean/IPRADerivations/Analysis/GaussianEulerUpperTailLeftNorm.lean)
uses it in the original upper-tail grid, with coefficient
`D_R=2^(R+1) R!` and the actual decay observation at `N/4` when
the grid starts at `N/2`. [GaussianEulerNamedUpperTail](Lean/IPRADerivations/Analysis/GaussianEulerNamedUpperTail.lean)
removes the auxiliary errors and proves the bound for the original
varying-cutoff upper-tail name.
[GaussianEulerUpperTailCauchyBudget](Lean/IPRADerivations/Analysis/GaussianEulerUpperTailCauchyBudget.lean)
applies the original cutoff height to that estimate.
[GaussianEulerLowerPowerComparison](Lean/IPRADerivations/Analysis/GaussianEulerLowerPowerComparison.lean)
checks the signed real upper bound for the actual lower-time power
square. [RationalHarmonicIntervalProduct](Lean/IPRADerivations/Analysis/RationalHarmonicIntervalProduct.lean)
checks the exact product telescope of the original finite harmonic intervals.
[GaussianHarmonicLogarithmPower](Lean/IPRADerivations/Analysis/GaussianHarmonicLogarithmPower.lean)
binds natural powers to the original logarithm. The transformed grid
and the sharp right-endpoint panel bound are checked by
[GaussianEulerLowerTailRootGrid](Lean/IPRADerivations/Analysis/GaussianEulerLowerTailRootGrid.lean)
and [GaussianEulerLowerTailPowerPanel](Lean/IPRADerivations/Analysis/GaussianEulerLowerTailPowerPanel.lean).
[GaussianEulerLowerTransformedIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerLowerTransformedIntegrand.lean)
proves the original pointwise estimate at those transformed times.
[GaussianEulerLowerTailLocalComparison](Lean/IPRADerivations/Analysis/GaussianEulerLowerTailLocalComparison.lean)
applies the actual sampled modulus to each row of the exact lower
partition and its right endpoint.
[GaussianEulerCompactLowerTail](Lean/IPRADerivations/Analysis/GaussianEulerCompactLowerTail.lean)
sums the weighted panel bounds through the exact original grouping.
[GaussianEulerLowerTailFiniteBudget](Lean/IPRADerivations/Analysis/GaussianEulerLowerTailFiniteBudget.lean)
and [GaussianEulerLowerCofinalQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerLowerCofinalQuadrature.lean)
give the cofinal norm bound and approximation to the actual lower name.
[GaussianEulerVaryingCutoffName](Lean/IPRADerivations/Analysis/GaussianEulerVaryingCutoffName.lean)
checks the actual varying-cutoff sampler and its regularity from the
lower-tail norm bound.
[GaussianEulerNamedLowerTail](Lean/IPRADerivations/Analysis/GaussianEulerNamedLowerTail.lean)
proves that bound on the original lower name at any requested observation
precision under the encoded positive half-plane hypotheses.
[GaussianEulerImproperName](Lean/IPRADerivations/Analysis/GaussianEulerImproperName.lean)
therefore gives regularity for the unchanged sampler and verifies its
primitive recursive output and evaluation schedule.
[GaussianEulerFixedCutoffApproximation](Lean/IPRADerivations/Analysis/GaussianEulerFixedCutoffApproximation.lean)
bounds its distance to the compact name at each fixed cutoff by the sum
of both tail majorants and the two independent observation errors.
[GaussianEulerUnitIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerUnitIntegrand.lean)
identifies the exact sample and finite grid at one with the decay program.
[GaussianEulerUnitEndpointDecay](Lean/IPRADerivations/Analysis/GaussianEulerUnitEndpointDecay.lean)
bounds the actual endpoint difference at the original cutoffs.
[GaussianEulerImproperNormalization](Lean/IPRADerivations/Analysis/GaussianEulerImproperNormalization.lean)
proves that the original improper Euler name at the canonical unit
argument agrees with the finite-product Gamma name at arbitrary
independent observation precisions.
[GaussianEulerBetaPoleGuard](Lean/IPRADerivations/Analysis/GaussianEulerBetaPoleGuard.lean)
proves the finite weighted Euler operator identity for the actual beta
primitive from the native positive half-plane source.
[GaussianBetaKernelLogarithm](Lean/IPRADerivations/Analysis/GaussianBetaKernelLogarithm.lean)
compares the original scaled logarithm with the decay exponent and gives
a fixed compact radius.
[GaussianBetaKernelSignedLogarithm](Lean/IPRADerivations/Analysis/GaussianBetaKernelSignedLogarithm.lean)
proves the finite Taylor sign and transfers it to the same original
rounded observation. The real remainder is at least the negative
dyadic allowance and obeys the original quadratic norm bound.
[GaussianBetaKernelDampedDoubling](Lean/IPRADerivations/Analysis/GaussianBetaKernelDampedDoubling.lean)
proves the exact one-step relative estimate for the original finite
kernel at degrees `N` and `2N`.
[GaussianBetaKernelDampedRefinement](Lean/IPRADerivations/Analysis/GaussianBetaKernelDampedRefinement.lean)
keeps the geometric factor and the actual later kernel throughout
finite dyadic refinement.
[GaussianBetaKernelDecayDampedError](Lean/IPRADerivations/Analysis/GaussianBetaKernelDecayDampedError.lean)
bounds the original kernel error by the quadratic factor times the
actual positive decay observation and its explicit allowances.
[GaussianBetaUpperRowDampedError](Lean/IPRADerivations/Analysis/GaussianBetaUpperRowDampedError.lean)
keeps the exact high-time row factor `t^(R+2)/N` with the same
positive decay reference and independently queried beta and Euler
observations. [GaussianEulerLowTimePowerOrder](Lean/IPRADerivations/Analysis/GaussianEulerLowTimePowerOrder.lean)
gives the reciprocal-power reference comparison for the actual
lower-time power square.
[GaussianEulerLowTimeReciprocalReference](Lean/IPRADerivations/Analysis/GaussianEulerLowTimeReciprocalReference.lean)
identifies that reference with the exact rational square, and
[GaussianEulerLowTimePowerBound](Lean/IPRADerivations/Analysis/GaussianEulerLowTimePowerBound.lean)
bounds the original lower-time power norm by `b/a+2^-p`.
[GaussianBetaKernelTailDifference](Lean/IPRADerivations/Analysis/GaussianBetaKernelTailDifference.lean)
bounds the absolute full-support kernel difference with one positive
decay factor and explicit observation allowances.
[GaussianBetaRowMonomialReference](Lean/IPRADerivations/Analysis/GaussianBetaRowMonomialReference.lean)
compares the actual high-time scalar majorant to the literal monomial
decay evaluator scaled by `1/N`.
[GaussianRationalQuadratureDifference](Lean/IPRADerivations/Analysis/GaussianRationalQuadratureDifference.lean)
binds the exact weighted sum of row differences to the original pair
of quadratures.
[GaussianMonomialDecayMajorant](Lean/IPRADerivations/Analysis/GaussianMonomialDecayMajorant.lean)
bounds the actual monomial times decay through the weighted half-decay
majorant at coefficient `2^d d!`.
[GaussianMonomialDecayQuadrature](Lean/IPRADerivations/Analysis/GaussianMonomialDecayQuadrature.lean)
and [GaussianMonomialDecayBudget](Lean/IPRADerivations/Analysis/GaussianMonomialDecayBudget.lean)
retain its integrated coefficient `2^(d+1) d!` above time one with
a computed dyadic allowance.
[GaussianEulerSharpDegreeSchedule](Lean/IPRADerivations/Analysis/GaussianEulerSharpDegreeSchedule.lean)
checks the report’s exact choice `N=4(C_R+D_R+p+10)·2^(p+4)`,
the rational bound `C_R/N≤2^(-p-3)`, and the original decay bound at
`N/4` with explicit observation error and a computed precision. The
full integrated sharp comparison remains.
[GaussianBetaLowGridError](Lean/IPRADerivations/Analysis/GaussianBetaLowGridError.lean)
proves the exact `1/N` contribution below time one from the actual
beta and Euler row observations, with independently requested errors.
[GaussianBetaUpperGridMonomialComparison](Lean/IPRADerivations/Analysis/GaussianBetaUpperGridMonomialComparison.lean)
proves the exact factorial cap divided by the degree for the actual
middle shared grid, with explicit mesh and evaluation allowances.
[GaussianBetaEulerTailDifferencePointwise](Lean/IPRADerivations/Analysis/GaussianBetaEulerTailDifferencePointwise.lean)
bounds the actual difference on the upper support by one factorial
half-decay reference and supplies the corresponding scalar majorant.
[GaussianBetaEulerUpperDifferenceGrid](Lean/IPRADerivations/Analysis/GaussianBetaEulerUpperDifferenceGrid.lean)
transfers that majorant on the original grid through a single
weighted half-decay quadrature.
[GaussianBetaZeroExtension](Lean/IPRADerivations/Analysis/GaussianBetaZeroExtension.lean)
keeps the literal beta evaluator on the support and returns the
canonical zero at the degree and beyond.
[GaussianBetaZeroExtendedGrid](Lean/IPRADerivations/Analysis/GaussianBetaZeroExtendedGrid.lean)
checks the finite support and exterior grid identities.
[GaussianCompactAlignedSplit](Lean/IPRADerivations/Analysis/GaussianCompactAlignedSplit.lean)
splits a shared mesh using actual equal-time observations, including
zero-width panels.
[GaussianBetaContiguousUpperTail](Lean/IPRADerivations/Analysis/GaussianBetaContiguousUpperTail.lean)
uses one factorially weighted original decay observation at a quarter
of the degree for the contiguous upper grid, with explicit sampling
and mesh allowances. The degree may be any fixed natural at least two.
[GaussianEulerSharpFiniteRate](Lean/IPRADerivations/Analysis/GaussianEulerSharpFiniteRate.lean)
connects those panels to the original finite Euler reciprocal-inverse
and improper Euler samplers. On the finite sampler domain `1 ≤ R`,
`2R ≤ N`, the checked distance has leading terms
`(1 + 2^(R+3) (R+2)!)/N` and `2^(R+1) R!` times the quarter-degree
decay observation's norm upper bound. That bound uses the exact raw
L1 radius of the original observation plus its own dyadic tolerance.
The finite and improper output clocks are independent and each retains
its own observation tolerance. An explicit finite clock eliminates the
auxiliary mesh and sampling errors inside the object theory.
[GaussianEulerDecayRealSamples](Lean/IPRADerivations/Analysis/GaussianEulerDecayRealSamples.lean)
proves that every original decay sample at a rational time is real.
Its raw L1 radius is its exact Euclidean absolute value.
[GaussianEulerSharpGammaRate](Lean/IPRADerivations/Analysis/GaussianEulerSharpGammaRate.lean)
transfers the exact radius to the original Gamma observation.
[GaussianEulerSharpScheduledApproximation](Lean/IPRADerivations/Analysis/GaussianEulerSharpScheduledApproximation.lean)
uses the stated degree `4(C_R+D_R+p+10)2^(p+4)` and proves that the
original finite observation at `p+2` is within `2^-p` of either
the original improper Euler or Gamma observation at `p+2`.
[GaussianBetaAllDegreeEulerInverse](Lean/IPRADerivations/Analysis/GaussianBetaAllDegreeEulerInverse.lean)
certifies the same finite reciprocal evaluator for all positive
degrees, using the height derived from its finite beta endpoint.
Its new data give the same represented value as the previous data
on the original sampler domain.
[GaussianEulerSharpAllDegrees](Lean/IPRADerivations/Analysis/GaussianEulerSharpAllDegrees.lean)
proves the sharp rate to the original improper sample for every
`N ≥ 2` on the encoded rational complex half-plane domain, with
independent output and decay precisions.
[GaussianEulerSharpReportTerms](Lean/IPRADerivations/Analysis/GaussianEulerSharpReportTerms.lean)
checks that each of the two leading terms is strictly below
`2^-(p+3)` at the stated degree and computed decay query.
[GaussianBetaAllDegreeMixedInverseContinuity](Lean/IPRADerivations/Analysis/GaussianBetaAllDegreeMixedInverseContinuity.lean)
proves a cutoff-independent input modulus for the actual all-degree
finite Euler evaluator with separately encoded rational inputs.
[GaussianEulerRealPowerLowerOrder](Lean/IPRADerivations/Analysis/GaussianEulerRealPowerLowerOrder.lean)
and [GaussianEulerDecayLowerEnvelope](Lean/IPRADerivations/Analysis/GaussianEulerDecayLowerEnvelope.lean)
prove the separate one-half and one-ninth lower estimates on the
original power and decay factors on the interval from one to two.
Each bound retains the tolerance of its actual requested observation.
[GaussianEulerSharpNamedIntegralRate](Lean/IPRADerivations/Analysis/GaussianEulerSharpNamedIntegralRate.lean)
extends the sharp rate to general fixed regular complex input names
with a positive real-part margin. It uses the input name's computed
disk radius and keeps the original improper integral observation.
[GaussianEulerSharpNamedSchedule](Lean/IPRADerivations/Analysis/GaussianEulerSharpNamedSchedule.lean)
checks the stated degree for the named Gamma observations.
[GaussianEulerIntegralPositiveLower](Lean/IPRADerivations/Analysis/GaussianEulerIntegralPositiveLower.lean)
sums the actual positive unit panel over the common mesh and proves
the bound one eighteenth, with the requested observation tolerance,
for the original improper integral and Gamma at encoded positive real inputs.
[GaussianNamedGammaPositiveLower](Lean/IPRADerivations/Analysis/GaussianNamedGammaPositiveLower.lean)
extends it to regular real names with actual real samples and a positive
real-part margin. [GaussianEulerUnitToTopBound](Lean/IPRADerivations/Analysis/GaussianEulerUnitToTopBound.lean)
gives the actual upper panel the factorial bound `2^(R+1) R!` with a
cofinal tolerance. [GaussianEulerEtaToOneRootGrid](Lean/IPRADerivations/Analysis/GaussianEulerEtaToOneRootGrid.lean)
checks the actual transformed mesh endpoints and right-row estimate
on the entire panel from the lower cutoff to one.
[GaussianEulerEtaToOneRowBound](Lean/IPRADerivations/Analysis/GaussianEulerEtaToOneRowBound.lean)
compares the original affine rows to those right endpoints.
[GaussianEulerEtaToOneQuadratureBound](Lean/IPRADerivations/Analysis/GaussianEulerEtaToOneQuadratureBound.lean)
sums the original weighted blocks.
[GaussianEulerEtaToOneBound](Lean/IPRADerivations/Analysis/GaussianEulerEtaToOneBound.lean)
gives the corresponding original compact observation radius `A + 2^(-p)`.
[GaussianEulerUnitToTopCompactBound](Lean/IPRADerivations/Analysis/GaussianEulerUnitToTopCompactBound.lean)
gives the observation from one the factorial radius with the requested
dyadic tolerance, and compares the actual compact samplers on a fixed
interval with different top guards.
[GaussianEulerIntegralUpperBound](Lean/IPRADerivations/Analysis/GaussianEulerIntegralUpperBound.lean)
uses the actual split at one to bound every original cutoff, then
[GaussianEulerIntegralUpperTransfer](Lean/IPRADerivations/Analysis/GaussianEulerIntegralUpperTransfer.lean)
gives the original improper and Gamma observation bounds with radius
`A + 2^(R+1) R! + 2^(-p)` for encoded inputs on the positive real
half-plane. The Gamma comparison uses the original guard `1 <= R`.
[GaussianNamedHalfPlaneCorrection](Lean/IPRADerivations/Analysis/GaussianNamedHalfPlaneCorrection.lean)
corrects late observations into the exact given half-plane without
changing the computed radius. [GaussianNamedGammaUpperBound](Lean/IPRADerivations/Analysis/GaussianNamedGammaUpperBound.lean)
then proves the same radius with the same `A` on regular complex names.
[GaussianEulerUnitNormalizationIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerUnitNormalizationIntegrand.lean)
identifies the original unit-argument samples with the decay samples.
[GaussianEulerUnitNormalizationCompact](Lean/IPRADerivations/Analysis/GaussianEulerUnitNormalizationCompact.lean)
uses the checked decay antiderivative on the original compact interval.
[GaussianEulerUnitNormalization](Lean/IPRADerivations/Analysis/GaussianEulerUnitNormalization.lean)
uses both endpoint bounds to derive the original improper integral value
one and hence the Gamma value one.
[GaussianEulerVerticalProjection](Lean/IPRADerivations/Analysis/GaussianEulerVerticalProjection.lean)
and [GaussianEulerVerticalNativeProjection](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNativeProjection.lean)
preserve the required disk and positive margin at the real part of the
argument. [GaussianEulerVerticalExponentialSquare](Lean/IPRADerivations/Analysis/GaussianEulerVerticalExponentialSquare.lean),
[GaussianEulerVerticalExponentReference](Lean/IPRADerivations/Analysis/GaussianEulerVerticalExponentReference.lean),
and [GaussianEulerVerticalIntegrandSquare](Lean/IPRADerivations/Analysis/GaussianEulerVerticalIntegrandSquare.lean)
identify the squared norms of the two original integrands.
[GaussianEulerVerticalRealSamples](Lean/IPRADerivations/Analysis/GaussianEulerVerticalRealSamples.lean)
and [GaussianEulerVerticalRealRadius](Lean/IPRADerivations/Analysis/GaussianEulerVerticalRealRadius.lean)
give the actual real-axis observations a nonnegative radius with a
dyadic correction. [GaussianPositiveRadiusFiniteSum](Lean/IPRADerivations/Analysis/GaussianPositiveRadiusFiniteSum.lean)
and [GaussianPositiveRadiusQuadrature](Lean/IPRADerivations/Analysis/GaussianPositiveRadiusQuadrature.lean)
carry certified row bounds through the unchanged finite weighted sums.
[GaussianEulerVerticalNormTransfer](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNormTransfer.lean)
transfers an actual sample radius across the squared norm identity.
[GaussianEulerVerticalPointwise](Lean/IPRADerivations/Analysis/GaussianEulerVerticalPointwise.lean)
then bounds each original complex row by its original real companion
and four requested dyadic allowances.
[GaussianEulerVerticalQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerVerticalQuadrature.lean)
gives the actual same-query compact and improper bounds with the precise
grid width and row precision.
[GaussianEulerVerticalShiftedRadius](Lean/IPRADerivations/Analysis/GaussianEulerVerticalShiftedRadius.lean)
keeps a nonnegative radius when a coarse real observation is signed.
[GaussianEulerVerticalGammaBound](Lean/IPRADerivations/Analysis/GaussianEulerVerticalGammaBound.lean)
proves the encoded-input vertical inequality on the original Gamma
observations at independent queries by removing the auxiliary improper
precision. [GaussianEulerVerticalNamedProjection](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNamedProjection.lean)
binds the real projection of a regular name to the decoded native
projection with the original disk.
[GaussianEulerVerticalNamedRadius](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNamedRadius.lean)
and [GaussianEulerVerticalNamedReference](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNamedReference.lean)
compare both actual named Gamma samplers to one late rational input and
its native real projection at a common certified radius.
[GaussianEulerVerticalNamedGammaBound](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNamedGammaBound.lean)
gives the same original vertical Gamma inequality at independent queries
of regular complex names, with only the two requested observation allowances.
[GaussianEulerVerticalNamedIntegralBound](Lean/IPRADerivations/Analysis/GaussianEulerVerticalNamedIntegralBound.lean)
proves the same inequality with the original named improper Euler
evaluators and the exact signed comparison radius.
[GaussianEulerIntegrationByPartsLinear](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsLinear.lean)
checks the original time-weighted product's linear term.
[GaussianEulerIntegrationByPartsProductStep](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsProductStep.lean)
and [GaussianEulerIntegrationByPartsStep](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsStep.lean)
give the literal original boundary increment its quadratic cell error
and explicit observation allowance.
[GaussianEulerIntegrationByPartsObservation](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsObservation.lean)
binds the literal power-times-decay product to the actual normalized
integrand at independent queries.
[GaussianEulerIntegrationByPartsGridObservation](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsGridObservation.lean)
carries this comparison to the actual weighted affine grid.
[GaussianEulerIntegrationByPartsEndpoints](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsEndpoints.lean)
bounds the original primitive at the lower cutoff and upper integer time.
[GaussianEulerIntegrationByPartsEndpointRescale](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsEndpointRescale.lean)
compares those times with their actual affine-grid endpoint encodings.
[GaussianEulerIntegrationByPartsGrid](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsGrid.lean)
telescopes the literal finite operator grid and retains an explicit
step and observation error.
[GaussianEulerIntegrationByPartsEndpointBudget](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsEndpointBudget.lean)
bounds each actual affine boundary observation at a computed later cutoff.
[GaussianEulerIntegrationByPartsCofinalGrid](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsCofinalGrid.lean)
chooses a refinement of the original compact mesh and reads the
same grid back to the original compact observations.
[GaussianEulerIntegrationByPartsNormalizedGrid](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsNormalizedGrid.lean)
relates the actual operator grid to the old and shifted normalized
Euler quadratures.
[GaussianEulerIntegrationByPartsRecurrence](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsRecurrence.lean)
combines those estimates with the original Euler-to-Gamma identification
to prove the right-half-plane recurrence on encoded rational inputs,
including the comparison at independent Gamma and product queries.
[GaussianEulerNamedIBPRecurrence](Lean/IPRADerivations/Analysis/GaussianEulerNamedIBPRecurrence.lean)
lifts this proof to original regular complex input names, using the
actual normalized translation by one and the original named product.
[GaussianEulerNamedIntegralIBPRecurrence](Lean/IPRADerivations/Analysis/GaussianEulerNamedIntegralIBPRecurrence.lean)
gives the corresponding identity of actual improper Euler names.
[GaussianEulerIntegrationByPartsCompact](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsCompact.lean)
keeps both actual shifted-integrand endpoint observations in the
finite compact identity, with a computed error.
[GaussianEulerIncompleteCutoff](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteCutoff.lean)
splits the original later compact name at any positive rational point
on a shared denominator and proves its actual compact additivity.
[GaussianEulerLogarithmicMultiplier](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicMultiplier.lean)
checks the actual logarithmic Euler rows for every numerical order.
[GaussianEulerLogarithmicCompactName](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCompactName.lean)
constructs their actual regular compact quadrature.
[GaussianUpperTimeLogarithmPower](Lean/IPRADerivations/Analysis/GaussianUpperTimeLogarithmPower.lean)
bounds the original regular logarithmic power on the upper half
of the time axis by the corresponding time power and observation error.
[GaussianEulerIntegrationByPartsCompactNamedIdentity](Lean/IPRADerivations/Analysis/GaussianEulerIntegrationByPartsCompactNamedIdentity.lean)
proves the regular-name compact identity on all encoded positive
intervals, including zero width, retaining both original boundary names.
[GaussianEulerIncompleteCutoffParts](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteCutoffParts.lean)
identifies the change in each actual compact piece at a fixed rational
split with the corresponding original whole-integral tail.
[GaussianEulerIncompleteCutoffRate](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteCutoffRate.lean)
bounds both changes using the original tail coefficients and the two
requested observation precisions.
[GaussianEulerIncompleteName](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteName.lean)
makes the cofinal lower and upper programs into actual regular names,
and [GaussianEulerIncompleteSum](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteSum.lean)
proves that their normalized sum agrees with the actual improper Euler
and Gamma names at every positive rational split.
[GaussianEulerIncompleteFixedCutoff](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteFixedCutoff.lean)
compares the incomplete names to their corresponding compact pieces
at any later fixed cutoff, with the original tail rate.
[GaussianEulerIncompleteRadiusOverlap](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteRadiusOverlap.lean)
aligns physical intervals across two certified radii and proves
agreement of the original names at independent queries.
[GaussianEulerIntegrandTimeProperness](Lean/IPRADerivations/Analysis/GaussianEulerIntegrandTimeProperness.lean)
identifies the original shifted integrand at equal rational encodings.
[GaussianEulerIncompleteRecurrence](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteRecurrence.lean)
proves both original incomplete recurrences, retaining the split-point
integrand with opposite signs and bounding the two external terms.
[GaussianEulerIncompleteUnitUpper](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteUnitUpper.lean)
identifies the original upper incomplete sampler at one with decay.
[GaussianEulerIncompleteFactorialDenominator](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteFactorialDenominator.lean)
checks the literal finite factorial polynomial, its original scalar
recurrence, and the integer numerator and denominator.
[GaussianEulerIntegerBoundary](Lean/IPRADerivations/Analysis/GaussianEulerIntegerBoundary.lean)
identifies the original integer boundary sampler with the literal
rational power times the original decay.
[GaussianEulerIncompleteIntegerFormula](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteIntegerFormula.lean)
derives the upper formula at every internal index by induction on
the fixed-precision numerical error.
[GaussianEulerIncompleteIntegerLowerFormula](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteIntegerLowerFormula.lean)
derives the lower formula from the original sum and factorial value.
[GaussianEulerIncompleteDyadicEndpoint](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteDyadicEndpoint.lean)
uses the original lower-tail bound to prove the exact root rate of
approach to the zero-split values on the original dyadic sequence.
[GaussianEulerIncompleteSmallRationalEndpoint](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteSmallRationalEndpoint.lean)
proves the same uniform bound for every positive rational split at most
the cutoff, with the original lower and upper programs and independent
requested observations.
[GaussianEulerIncompleteZeroModulus](Lean/IPRADerivations/Analysis/GaussianEulerIncompleteZeroModulus.lean)
computes a positive rational threshold directly from any requested
endpoint tolerance.
[GaussianLogarithmFactorialPowerBound](Lean/IPRADerivations/Analysis/GaussianLogarithmFactorialPowerBound.lean)
derives the literal logarithmic power bound from the corresponding
factorial term of the original finite exponential.
[GaussianEulerLogarithmicHalfDecay](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicHalfDecay.lean)
proves the upper weighted-row bound at the exact factorial majorant
for the combined Euler and logarithmic degree.
[GaussianEulerLowerLogarithmPower](Lean/IPRADerivations/Analysis/GaussianEulerLowerLogarithmPower.lean)
proves the inverse-root bound for the actual logarithm at squared root times.
[GaussianEulerLogarithmicUpperPointwise](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicUpperPointwise.lean)
proves the original upper pointwise majorant for the retimed logarithmic compact row.
[GaussianEulerLogarithmicUpperScalar](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicUpperScalar.lean)
supplies the original scalar majorant at the combined degree to the actual compact evaluator.
[GaussianEulerLogarithmicUpperCutoffBudget](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicUpperCutoffBudget.lean)
checks the actual upper logarithmic compact tails at the integer cutoff
with the exact doubled upper factorial coefficient.
[GaussianEulerLogarithmicLowerFiniteBudget](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicLowerFiniteBudget.lean)
checks the actual finite lower logarithmic root quadrature with the
exact factorial coefficient at the doubled root degree.
[GaussianEulerLogarithmicNamedLowerBound](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicNamedLowerBound.lean)
and [GaussianEulerLogarithmicLowerCutoffBudget](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicLowerCutoffBudget.lean)
lift the bound to the actual compact lower name and compute a cutoff
for any requested tail tolerance.
[GaussianEulerLogarithmicIntervalAdditivity](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicIntervalAdditivity.lean)
checks finite additivity at fixed evaluator guards.
[GaussianEulerLogarithmicClientRate](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicClientRate.lean)
proves the original logarithmic rows agree when the evaluator guards change.
[GaussianEulerLogarithmicClientIndependence](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicClientIndependence.lean)
lifts that agreement to the actual compact names.
[GaussianEulerLogarithmicLowerGuardBound](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicLowerGuardBound.lean)
preserves the exact lower coefficient under a larger valid upper-time guard.
[GaussianEulerLogarithmicCommonCutoff](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCommonCutoff.lean)
identifies the physical cutoff intervals using a computed lower index offset,
with the original integrand radius retained.
[GaussianEulerLogarithmicCertificateGeometry](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCertificateGeometry.lean)
matches the actual lower endpoints for two independent cutoff certificates.
[GaussianEulerLogarithmicImproperName](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicImproperName.lean)
constructs the actual regular varying-cutoff name at every numerical
logarithmic order.
[GaussianEulerLogarithmicFixedCutoff](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicFixedCutoff.lean)
proves an independent observation rate to any sufficiently late fixed interval.
[GaussianEulerLogarithmicTopExtension](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicTopExtension.lean)
compares an actual compact cutoff with its extension to an arbitrary larger top.
[GaussianEulerLogarithmicCertificateOverlap](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCertificateOverlap.lean),
[GaussianEulerLogarithmicInputProperness](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicInputProperness.lean),
and [GaussianEulerLogarithmicImproperInputProperness](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicImproperInputProperness.lean)
prove agreement across independent certificates and equal normalized rational inputs.
[GaussianEulerLogarithmicContinuity](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicContinuity.lean)
computes a parameter modulus and proves the independent observation estimate
for the original improper names on certified rational shifts.
[GaussianEulerLogarithmicZeroIdentification](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicZeroIdentification.lean)
identifies the order-zero improper name with the original Gamma program.
[GaussianEulerLogarithmicParameterTaylor](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicParameterTaylor.lean)
checks the actual pointwise first-order remainder at every numerical
order. It derives the shifted radius from the increment bound and
leaves all three original observation queries independent.
[GaussianEulerLogarithmicTaylorGrid](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicTaylorGrid.lean)
integrates the actual quadratic bound on a shared finite grid with
the exact interval-length factor.
[GaussianEulerLogarithmicCompactTaylor](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCompactTaylor.lean)
lifts the finite estimate to the three independently meshed compact
names and retains the exact quadratic coefficient.
[GaussianEulerLogarithmicCompactParameterRate](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicCompactParameterRate.lean)
derives a fixed-interval parameter Lipschitz estimate from that bound
and the actual compact majorant at the next logarithmic order.
[GaussianEulerDerivativeParameterPath](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeParameterPath.lean)
and [GaussianEulerDerivativeSubdivisionBudget](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeSubdivisionBudget.lean)
verify the native parameter segment, its endpoint and step identities,
and the computed subdivision and relative error budgets.
[GaussianEulerDerivativeSlopeVariation](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeSlopeVariation.lean)
bounds variation of the original improper slopes along the whole path, uniformly
in its subdivision count.
[GaussianEulerLogarithmicPathCompactTaylor](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicPathCompactTaylor.lean)
checks the exact local remainder on successive original compact path observations.
[GaussianEulerDerivativeCommonInterval](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeCommonInterval.lean)
constructs a common physical interval for adjacent orders at every path point
and preserves the independently chosen truncation tolerances.
[GaussianRationalParameterTelescope](Lean/IPRADerivations/Analysis/GaussianRationalParameterTelescope.lean)
sums the finite parameter errors and converts the repeated substep to the actual
whole increment.
[GaussianEulerLogarithmicPathCompactRows](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicPathCompactRows.lean)
and [GaussianEulerDerivativeCompactSlopeRows](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeCompactSlopeRows.lean)
supply the two actual finite row tables.
[GaussianEulerDerivativeEndpointBinding](Lean/IPRADerivations/Analysis/GaussianEulerDerivativeEndpointBinding.lean)
transports the two compact endpoints to the original improper names.
[GaussianNamedDifferenceQuotient](Lean/IPRADerivations/Analysis/GaussianNamedDifferenceQuotient.lean)
constructs the actual regular difference quotient for a nonzero native increment.
[GaussianRationalNormalizedTelescope](Lean/IPRADerivations/Analysis/GaussianRationalNormalizedTelescope.lean)
cancels the increment before bounding the finite mean of the slope errors.
[GaussianEulerLogarithmicDerivative](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicDerivative.lean)
proves `I_j' = I_{j+1}` of ledger family 14 on certified native Gaussian
rational inputs for every numerical `j`. Its modulus is independent of the
increment, and the bound is `2⁻ᵖ + 2⁻ᑫ + 2⁻ᵛ` for the independent actual
observations at `q` and `v`.
[GaussianGammaEulerFirstDerivative](Lean/IPRADerivations/Analysis/GaussianGammaEulerFirstDerivative.lean)
binds the quotient made directly from the original Gamma evaluator to
the certified order-one logarithmic integral at the same rate.
[GaussianGammaUnitEulerDifference](Lean/IPRADerivations/Analysis/GaussianGammaUnitEulerDifference.lean)
gives the explicit positive rational increment schedule at one.
[GaussianRationalUnitInverseExpansion](Lean/IPRADerivations/Analysis/GaussianRationalUnitInverseExpansion.lean)
transports a finite quadratic remainder through inversion using the
actual product residual.
[GaussianGammaDerivativeAtOne](Lean/IPRADerivations/Analysis/GaussianGammaDerivativeAtOne.lean)
identifies the original first logarithmic Euler integral at one with
the negative of the original Euler–Mascheroni name. The independent
Gamma difference-quotient observations have the same dyadic derivative
rate for every increment certified by the original Euler derivative
source, including the computed positive rational steps.
[GaussianEulerLogarithmicMixedParameterRate](Lean/IPRADerivations/Analysis/GaussianEulerLogarithmicMixedParameterRate.lean)
proves the uniform comparison at distinct native inputs with independent
certificates. [GaussianNamedEulerLogarithmicImproper](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicImproper.lean)
uses a finite demand maximum to construct regular logarithmic improper
evaluators at every numerical order on a fixed certified complex name.
[GaussianRationalQuadratureDilation](Lean/IPRADerivations/Analysis/GaussianRationalQuadratureDilation.lean)
checks the finite pullback for a positive rational scale and its exact
Jacobian, preserving the original grid observations.
[GaussianEulerPositiveTimePowerProduct](Lean/IPRADerivations/Analysis/GaussianEulerPositiveTimePowerProduct.lean)
proves the product laws for the original positive-time logarithm and complex power.
[GaussianEulerPositiveScalingIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerPositiveScalingIntegrand.lean)
proves the actual pointwise pullback identity with modified decay and the
original complex power factor.
[GaussianNamedEulerLogarithmicFrozenRate](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicFrozenRate.lean)
compares the named integral with any sufficiently late decoded input.
[GaussianNamedEulerLogarithmicIncrementBinding](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicIncrementBinding.lean)
uses one decoded base value and its exact Gaussian rational shift.
[GaussianNamedEulerLogarithmicDerivative](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicDerivative.lean)
proves family 14 at every numerical order on any fixed certified regular
complex name, for nonzero native Gaussian rational increments. It preserves
both requested observation precisions and computes the modulus before the
increment is supplied.
[GaussianNamedEulerLogarithmicNamedDerivative](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicNamedDerivative.lean)
extends the same estimate to increments given by regular complex names
with finite apartness and an all-observation smallness certificate. The
actual named reciprocal, original difference, and original named slope
all retain their original query interfaces.
[GaussianNamedEulerLogarithmicZeroIdentification](Lean/IPRADerivations/Analysis/GaussianNamedEulerLogarithmicZeroIdentification.lean)
proves that the order-zero evaluator agrees with the original Gamma name
on every fixed certified complex input.
[GaussianNamedGammaEulerFirstDerivative](Lean/IPRADerivations/Analysis/GaussianNamedGammaEulerFirstDerivative.lean)
proves the first derivative estimate directly for the quotient of the original
named Gamma evaluators along a certified regular named increment.
[GaussianEulerPositiveScalingQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerPositiveScalingQuadrature.lean)
lifts the scaled integrand identity to the original finite quadrature
with its rational Jacobian and both observation allowances.
[GaussianEulerPositiveScalingCompact](Lean/IPRADerivations/Analysis/GaussianEulerPositiveScalingCompact.lean)
compares the resulting compact names on a common rational grid.
[GaussianEulerPositiveScalingImproper](Lean/IPRADerivations/Analysis/GaussianEulerPositiveScalingImproper.lean)
checks family 16 at exponent parameter `r = 1` with a positive rational
damping rate `c / d` and encoded complex input. The compact damped
samples on the inverse-dilated Euler cutoffs form a regular improper
name. Its independent observations agree with the original improper
Euler integral multiplied by the actual inverse scale power
`exp(-(z / B) log(c / d))` within the sum of the two dyadic errors.
[GaussianEulerPositiveScalingGamma](Lean/IPRADerivations/Analysis/GaussianEulerPositiveScalingGamma.lean)
identifies the resulting improper name directly with the original
Gamma name times this inverse scale power and proves the forward
identity obtained by multiplying the integral by the positive scale power.
[GaussianRationalQuadratureSquareJacobian](Lean/IPRADerivations/Analysis/GaussianRationalQuadratureSquareJacobian.lean)
checks the finite left-endpoint Jacobian error for the quadratic map.
[GaussianEulerSquarePower](Lean/IPRADerivations/Analysis/GaussianEulerSquarePower.lean)
checks the original power at a squared rational time against the
original-time evaluator with doubled exponent.
[GaussianEulerSquareIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerSquareIntegrand.lean)
identifies the actual Jacobian-weighted Euler observation with the
doubled-power kernel times twice the scale power. It preserves the
finite evaluator and its original product query.
[GaussianRationalQuadratureSquareGridDistance](Lean/IPRADerivations/Analysis/GaussianRationalQuadratureSquareGridDistance.lean)
locates the target grid blocks and checks their mapped node distances.
[GaussianEulerQuadraticLowerEndpoint](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticLowerEndpoint.lean)
checks cofinal containment and the actual lower omitted-tail bound
at the mapped rational endpoints.
[GaussianEulerSquareCompactComparison](Lean/IPRADerivations/Analysis/GaussianEulerSquareCompactComparison.lean)
proves the original compact Euler integral equals the retimed
Jacobian-weighted compact integral on positive-width rational
intervals. It retains both requested observation precisions. The
zero-width finite quadratures both evaluate to zero.
[GaussianEulerQuadraticKernelCompactName](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticKernelCompactName.lean)
constructs the regular compact sampler for the unfactored kernel.
[GaussianEulerQuadraticUpperEndpoint](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticUpperEndpoint.lean)
aligns a quadratic image endpoint to an original upper cutoff and
bounds the actual omitted upper tail.
[GaussianEulerQuadraticImproperJacobian](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticImproperJacobian.lean)
checks the cofinal Jacobian-weighted integral against the original
Gamma evaluator. [GaussianEulerQuadraticImproperKernel](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticImproperKernel.lean)
constructs the separate cofinal sampler for the unfactored kernel
and proves its inverse-factor identity with the original Euler name.
[GaussianEulerQuadraticGamma](Lean/IPRADerivations/Analysis/GaussianEulerQuadraticGamma.lean)
checks the quadratic family 15 identity
\(\Gamma(z)=2c^z\int_0^\infty u^{2z-1}e^{-cu^2}\,du\)
for positive rational \(c\) and certified encoded complex \(z\),
with independent observation precisions for the original Gamma
name and the actual factored improper sampler.
[GaussianEulerExponentialSubstitutionNamedKernel](Lean/IPRADerivations/Analysis/GaussianEulerExponentialSubstitutionNamedKernel.lean)
constructs the actual exponential kernel on a regular input name
and identifies its value at the original logarithm of a positive
rational time. [GaussianEulerExponentialLogGrid](Lean/IPRADerivations/Analysis/GaussianEulerExponentialLogGrid.lean)
checks the finite logarithmic image sum using the actual widths
and the exponential values at the mapped left endpoints.
[GaussianEulerUnitSubstitutionDensity](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionDensity.lean)
compares the finite original decay-image density to the original
Euler quadrature. [GaussianEulerUnitLogarithmicComposition](Lean/IPRADerivations/Analysis/GaussianEulerUnitLogarithmicComposition.lean)
constructs the actual logarithm of minus log at rational inputs
strictly between zero and one.
[GaussianEulerExponentialImproper](Lean/IPRADerivations/Analysis/GaussianEulerExponentialImproper.lean)
identifies the original Gamma name with the improper sampler of
$e^{zu-e^u}$ on the logarithmic images of the original Euler grids.
[GaussianEulerExponentialLogPartition](Lean/IPRADerivations/Analysis/GaussianEulerExponentialLogPartition.lean)
proves nonnegative sampled widths, the $C/N$ mesh bound and exact
telescoping. [GaussianEulerExponentialCutoffPartition](Lean/IPRADerivations/Analysis/GaussianEulerExponentialCutoffPartition.lean)
proves that the actual image endpoints exhaust every fixed signed
interval. [GaussianEulerExponentialNamedKernelRate](Lean/IPRADerivations/Analysis/GaussianEulerExponentialNamedKernelRate.lean)
checks the uniform gain for the genuine kernel on regular names.
[GaussianEulerUnitSubstitutionGamma](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionGamma.lean)
identifies the actual cofinal decay-image density on `u = exp(-t)`
with the original Gamma name. [GaussianEulerUnitSubstitutionImageGrid](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionImageGrid.lean)
checks order, total width and shrinking mesh, and
[GaussianEulerUnitSubstitutionEndpoints](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionEndpoints.lean)
checks exhaustion to zero and one.
[GaussianEulerUnitKernelCompactRate](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelCompactRate.lean)
certifies the genuine rational-input kernel on compact subintervals
of `(0, 1)`.
[GaussianNamedEulerUnitKernel](Lean/IPRADerivations/Analysis/GaussianNamedEulerUnitKernel.lean)
extends the actual kernel to regular names whose real samples remain
in the certified compact interval. It derives regularity and
properness from the literal decoded rational samples and their
computed observation precisions.
[GaussianNamedEulerUnitKernelFrozenRate](Lean/IPRADerivations/Analysis/GaussianNamedEulerUnitKernelFrozenRate.lean)
compares the actual result with the original rational kernel at any
frozen input sample, with leading error `L / 2^k` and both requested
dyadic allowances.
[GaussianNamedEulerUnitTime](Lean/IPRADerivations/Analysis/GaussianNamedEulerUnitTime.lean)
constructs the original harmonic logarithmic time on those inputs.
[GaussianNamedEulerUnitTimeExponential](Lean/IPRADerivations/Analysis/GaussianNamedEulerUnitTimeExponential.lean)
recovers the original input by exponentiating the negative of its time.
[GaussianEulerUnitDecayInput](Lean/IPRADerivations/Analysis/GaussianEulerUnitDecayInput.lean)
supplies the exact compact certificate for the original decay at a
computed later precision. For `1/E <= t <= T`, that certificate is
`[1/G, 1-1/G]` with `G = 2(3^T + 4E)`.
[GaussianRealNameExponentialInjectivity](Lean/IPRADerivations/Analysis/GaussianRealNameExponentialInjectivity.lean)
derives equality of the original real-axis inputs from equality of
their separately clocked exponentials.
[GaussianNamedEulerUnitKernelAtDecay](Lean/IPRADerivations/Analysis/GaussianNamedEulerUnitKernelAtDecay.lean)
proves that the actual time at `u = exp(-t)` equals `t`, and that
the genuine named kernel at that input equals the original Euler
power at `t`, with independent precision allowances. It also bounds
the error of evaluating the rational unit kernel at a literal
rounded decay sample.
[GaussianEulerUnitSubstitutionDensityPrecision](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionDensityPrecision.lean)
gives a uniform bound for independently late observations of the
same fixed-grid density.
[GaussianEulerUnitSubstitutionTiltedNodes](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionTiltedNodes.lean)
gives ordered native rational nodes with an explicit correction of
at most `2N / 2^p` for each original rounded decay node.
[RationalUnitFloorBounds](Lean/IPRADerivations/Analysis/RationalUnitFloorBounds.lean)
derives compact interval guards for quantized lattice nodes and all
intermediate points. [RationalTiltedFloorWidth](Lean/IPRADerivations/Analysis/RationalTiltedFloorWidth.lean)
bounds each rounded width by the original signed width, with one
tilt increment and the two floor allowances.
[GaussianEulerUnitSubstitutionReversedWeights](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionReversedWeights.lean)
keeps the original density under exact finite reversal and projects
the actual cell mesh to scalar endpoint distances.
[GaussianEulerUnitKernelCompactName](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelCompactName.lean)
constructs a regular compact unit-kernel quadrature with an explicit
modulus on native rational panels.
[GaussianEulerUnitSubstitutionNearbyKernel](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionNearbyKernel.lean)
bounds the original power against the rational kernel at nearby
points with independent observation precisions.
[GaussianPartitionedFiniteSumTotalDistance](Lean/IPRADerivations/Analysis/GaussianPartitionedFiniteSumTotalDistance.lean)
accumulates the finite row error using the total cut width.
[GaussianPartitionedFiniteSumWeightReplacement](Lean/IPRADerivations/Analysis/GaussianPartitionedFiniteSumWeightReplacement.lean)
controls the replacement of the integer-cell weights by signed widths.
[GaussianEulerUnitSubstitutionFloorCuts](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionFloorCuts.lean)
constructs the absolute and relative integer cuts in a common
certified compact unit interval.
[GaussianEulerUnitSubstitutionLatticeComparison](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionLatticeComparison.lean)
compares the original signed decay-image density to the original
unit kernel evaluated on the resulting uniform rational lattice.
The error includes the original mesh and pointwise rate and the
summed cost of replacing the signed cell widths.
[GaussianEulerUnitSubstitutionLatticeRate](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionLatticeRate.lean)
separates the finite error into the time mesh, decay precision,
lattice denominator and independent kernel precision.
[GaussianEulerUnitSubstitutionIndependentQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionIndependentQuadrature.lean)
extends this finite comparison to an independently chosen positive
uniform quadrature count at independent precision on the same
rational panel, including a collapsed rounded panel.
[GaussianEulerUnitSubstitutionPanelComparison](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionPanelComparison.lean)
compares the original regular compact unit quadrature on a computed
rational panel to any independently requested observation of the original
compact Euler name.
[GaussianEulerUnitSubstitutionOrdinaryImproper](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionOrdinaryImproper.lean)
identifies the resulting cofinal ordinary unit quadrature with the original
Gamma name, with independent observation indices. Its Euler comparison
allows any later original time cutoff.
[GaussianEulerUnitSubstitutionOrdinaryEndpoints](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionOrdinaryEndpoints.lean)
proves that the same rounded rational endpoints are strictly inside the
unit interval and approach zero and one with the requested dyadic errors.
[GaussianEulerUnitKernelRationalPanelContinuity](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelRationalPanelContinuity.lean)
bounds the difference of the actual compact unit quadratures on two
panels in a common certified compact interval. Both endpoints may
move by a given rational radius and the two rational denominators
and observation indices may be chosen independently. The leading
error is the endpoint radius times the sum of the compact Lipschitz
constant and twice the kernel majorant.
[GaussianEulerUnitKernelMarginIndependence](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelMarginIndependence.lean)
proves that changing the certified margin on a fixed panel preserves
the original name.
[GaussianEulerUnitSubstitutionOrdinaryContainment](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionOrdinaryContainment.lean)
shows that the actual rounded cofinal panel contains any fixed proper
rational panel as soon as its stage unit reaches that panel's denominator.
[GaussianEulerUnitKernelNestedPanels](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelNestedPanels.lean)
splits the actual compact quadrature on a containing rational panel
into the original contained quadrature and the two omitted strips.
The two original panels can have different denominators and compact
margins, and either strip can have width zero.
[GaussianEulerUnitKernelCompactDominance](Lean/IPRADerivations/Analysis/GaussianEulerUnitKernelCompactDominance.lean)
bounds the norm of each original compact observation by the real
part of the original quadrature at the projected parameter, plus
both requested observation errors.
[GaussianEulerUnitSubstitutionArbitraryExhaustion](Lean/IPRADerivations/Analysis/GaussianEulerUnitSubstitutionArbitraryExhaustion.lean)
proves the uniform ordinary improper limit for encoded complex inputs
on the certified right half-plane. For target precision `s`, the
denominator of the computed inner reference panel gives a reciprocal
endpoint tolerance. Any proper rational panel within that tolerance
has original compact observation `p` within
`2^(-s) + 2^(-p) + 2^(-q)` of the original Gamma observation `q`.
The proof accepts any valid compact margin. The panel denominator
automatically supplies one for every proper rational panel.
[GaussianEulerPositivePowerChart](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChart.lean)
constructs the actual power chart for positive rational scale and
exponent with compact variation bounds.
[GaussianEulerPositivePowerChartJacobian](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartJacobian.lean)
evaluates the Jacobian of the same chart and bounds the quadratic
increment remainder at independent observation precisions.
[GaussianEulerPositivePowerChartOrder](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartOrder.lean) proves order on rational times with the two independent
dyadic observation allowances. [GaussianEulerPositivePowerChartLogarithm](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartLogarithm.lean) identifies the original
chart with the exponential of its affine logarithmic coordinate.
[GaussianEulerPowerScalingParameter](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingParameter.lean) derives the rescaled native Gamma parameter and
its half-plane source. [GaussianEulerPowerScalingKernel](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingKernel.lean) proves the pointwise kernel
identity including the inverse scale factor and the rescaled complex
exponent. [GaussianEulerPositivePowerChartLower](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartLower.lean) supplies an explicit positive lower bound on
the compact image and exact positive-real sample guards at uniformly
late precisions. [GaussianEulerDampedNamedIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerDampedNamedIntegrand.lean) identifies the original power-damped Euler
integrand times t with the logarithmic kernel. [GaussianEulerPowerScalingCompactRate](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingCompactRate.lean) gives a
uniform majorant and a compact variation bound for the actual
power-damped integrand. [GaussianEulerPositivePowerChartImage](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartImage.lean) decodes the original retimed chart
samples as exact positive rationals. [GaussianEulerPositivePowerChartMesh](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartMesh.lean) gives ordered corrected
image nodes and a finite mesh bound. [GaussianEulerPositivePowerChartMeshJacobian](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartMeshJacobian.lean) compares individual
corrected widths with the original Jacobian times the physical step and
gives the exact correction on a repeated cell. [GaussianNamedPositiveLogarithm](Lean/IPRADerivations/Analysis/GaussianNamedPositiveLogarithm.lean) extends the original
positive-rational logarithm to compact positive names, and [GaussianNamedPositiveLogarithmExponential](Lean/IPRADerivations/Analysis/GaussianNamedPositiveLogarithmExponential.lean)
recovers the named input under the original exponential. [GaussianEulerPowerChartNamedLogarithm](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartNamedLogarithm.lean)
identifies the lifted chart logarithm with its affine coordinate.
[GaussianEulerPowerChartFrozenKernel](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartFrozenKernel.lean) gives the compact comparison with the literal time-weighted
Euler row at the frozen decoded image. [GaussianEulerPowerScalingFrozenIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingFrozenIntegrand.lean) cancels the
source time and compares the original power-damped integrand directly
to the frozen Euler row with its inverse scale factor. [GaussianEulerPowerScalingCompactName](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingCompactName.lean)
builds the ordinary source-panel quadrature. [GaussianEulerPowerScalingFrozenRow](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingFrozenRow.lean) exposes the exact
original row clocks, and [GaussianEulerPowerScalingCell](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingCell.lean) combines their readback with the
evaluated Jacobian error. [GaussianEulerPowerScalingImageQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingImageQuadrature.lean) compares the finite affine source sum
with the corrected image sum and extracts one original scale factor.
[GaussianEulerPositivePowerChartCorrectedImage](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartCorrectedImage.lean) decodes the corrected nodes in a certified compact interval
and compares their original Euler samples to those at the raw image.
[GaussianEulerPowerScalingCorrectedQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingCorrectedQuadrature.lean) lifts that comparison to the full finite weighted sum.
[GaussianEulerPowerScalingFiniteSubstitution](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingFiniteSubstitution.lean) combines both finite comparisons with the source-derived
rescaled Gamma parameter and a single common scale observation.
[GaussianEulerPowerScalingFiniteBudget](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingFiniteBudget.lean) separates the mesh and observation errors. [GaussianEulerPowerScalingGridSchedule](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingGridSchedule.lean) gives
an explicit count and two clocks for an arbitrary dyadic accuracy
request. The scheduled source grid refines the unchanged compact
quadrature mesh and gives a comparison to the actual compact name.
[GaussianEulerPositivePowerChartCorrectedPanel](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartCorrectedPanel.lean) proves the corrected nodes lie in their exact rational
endpoint panel and gives a common denominator for the two endpoints.
[GaussianEulerPowerChartRationalPowers](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartRationalPowers.lean) evaluates chart values at native rational powers. [GaussianEulerPowerChartRoundedEndpoints](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartRoundedEndpoints.lean)
controls both actual rounded endpoints. [GaussianEulerPowerChartCofinalSchedule](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartCofinalSchedule.lean) then derives corrected
panels enclosing any prescribed original Euler cutoff while using the
same grid schedule as the finite substitution.
[GaussianEulerPositivePowerChartImageComparison](Lean/IPRADerivations/Analysis/GaussianEulerPositivePowerChartImageComparison.lean) compares the literal weighted rows to independently counted
ordinary Euler quadratures on the exact corrected panel by refinement
on a common native lattice. [GaussianEulerCompactExhaustion](Lean/IPRADerivations/Analysis/GaussianEulerCompactExhaustion.lean) compares arbitrary enclosing
ordinary quadratures to the unchanged improper Gamma name. [GaussianEulerCompactExhaustionScaled](Lean/IPRADerivations/Analysis/GaussianEulerCompactExhaustionScaled.lean)
gives a dyadic schedule with the original inverse scale observation,
and [GaussianEulerCompactExhaustionNormalization](Lean/IPRADerivations/Analysis/GaussianEulerCompactExhaustionNormalization.lean) supplies the paid-clock cancellation of the chart coefficient.
[GaussianEulerPowerScalingCofinalObservation](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingCofinalObservation.lean) composes the finite substitution and two ordinary image
comparisons with independent observation precisions. [GaussianEulerPowerScalingSourceExhaustion](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingSourceExhaustion.lean) proves
that these physical source panels eventually contain every fixed positive
rational interval. [GaussianEulerPowerScalingImproper](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingImproper.lean) compiles the ordinary panel observations
into the original cofinal improper sampler and derives its equality with
`(1/r) c^(-z/r) Γ(z/r)` for every positive rational `c,r` under the
original encoded right-half-plane assumptions.
[GaussianNamedPositiveReciprocal](Lean/IPRADerivations/Analysis/GaussianNamedPositiveReciprocal.lean) gives a regular name by taking exact reciprocals of
literal retimed observations. [GaussianEulerNamedPowerScalingParameter](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingParameter.lean) derives the positive
half-plane margin at the named argument `z/r`, and [GaussianEulerNamedPowerScalingFormula](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingFormula.lean) constructs
the regular Gamma-side product with the original exponential. On
compact intervals, [GaussianNamedDampingPowerChart](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerChart.lean) gives a joint rate in the two parameter
names and the time. [GaussianNamedDampingPowerIntegrand](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerIntegrand.lean) specializes the original named kernel
exactly to constant rational parameters, and [GaussianNamedDampingPowerFrozen](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerFrozen.lean) derives its
uniform pointwise rate to the original kernel at literal decoded
rational parameter observations.
[GaussianNamedDampingPowerCompact](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerCompact.lean) constructs the original compact quadrature name for positive
parameter names. [GaussianNamedDampingPowerCompactPaid](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerCompactPaid.lean) chooses a common freezing clock on each fixed
physical panel, and [GaussianNamedDampingPowerCompactAdditivity](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerCompactAdditivity.lean) checks addition across adjacent panels.
[GaussianNamedDampingPowerCompactBound](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerCompactBound.lean) transfers rational panel bounds with a dyadic allowance. [GaussianEulerNamedPowerScalingGammaFrozen](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingGammaFrozen.lean)
gives the independent rate for the actual Gamma at the named and exact
payload rational arguments. [GaussianEulerPowerChartExponentOrder](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartExponentOrder.lean) orders the rational charts by
exponent on either side of one using their original observations.
[GaussianEulerPowerChartUniformRounded](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartUniformRounded.lean) and [GaussianEulerPowerScalingUniformObservation](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingUniformObservation.lean) choose physical endpoints before either parameter
is frozen, then compare the original enclosing rational quadrature. [GaussianEulerPowerChartUniformExhaustion](Lean/IPRADerivations/Analysis/GaussianEulerPowerChartUniformExhaustion.lean)
proves cofinality of those physical panels. [GaussianEulerNamedPowerScalingFormulaFrozen](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingFormulaFrozen.lean) gives the independent
rate for the full named Gamma product. [GaussianEulerNamedPowerScalingImproper](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingImproper.lean) identifies the actual
cofinal ordinary quadrature with that product for all certified positive
names. [GaussianNamedDampingPowerLowerCutoff](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerLowerCutoff.lean) gives the independent compact lower-cutoff bound on the
original root grid, including zero width. [GaussianNamedDampingPowerReciprocalTail](Lean/IPRADerivations/Analysis/GaussianNamedDampingPowerReciprocalTail.lean) checks a finite
affine-grid reciprocal-square comparison.
[GaussianEulerNamedPowerScalingExhaustion](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingExhaustion.lean) identifies the exact selected named panel and proves that it
eventually encloses each fixed positive rational interval. [GaussianEulerPowerScalingArbitraryObservation](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingArbitraryObservation.lean)
and [GaussianEulerNamedPowerScalingArbitraryPanel](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingArbitraryPanel.lean) prove the rate for any enclosing positive rational physical
panel with arbitrary independent observation precisions.
[GaussianEulerNamedPowerScalingArbitraryLimit](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingArbitraryLimit.lean) binds the arbitrary enclosing panels directly to the actual
named improper sampler, and [GaussianEulerPowerScalingArbitraryTails](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingArbitraryTails.lean) and [GaussianEulerNamedPowerScalingArbitraryTails](Lean/IPRADerivations/Analysis/GaussianEulerNamedPowerScalingArbitraryTails.lean) give the explicit norm
bounds for panels lying wholly outside either physical cutoff.
[GaussianBetaSharpPartition](Lean/IPRADerivations/Analysis/GaussianBetaSharpPartition.lean)
locates one and the two degree endpoints on the same original dyadic
grid and identifies the original half-time decay at the split with
the literal quarter-degree observation.
[GaussianBetaKernelGridComparison](Lean/IPRADerivations/Analysis/GaussianBetaKernelGridComparison.lean)
compares the literal finite beta-kernel grid with the original improper
Euler observation at its actual evaluation clock and also allows
independent observation precision on a fixed cutoff interval.
[GaussianEulerBetaProductValue](Lean/IPRADerivations/Analysis/GaussianEulerBetaProductValue.lean)
identifies the original reciprocal head with the factorial quotient
of the actual rising product.
[GaussianGammaHalfEulerHead](Lean/IPRADerivations/Analysis/GaussianGammaHalfEulerHead.lean) evaluates the original finite head at one half and checks
its exact inverse product. [GaussianGammaHalfEulerExponential](Lean/IPRADerivations/Analysis/GaussianGammaHalfEulerExponential.lean) proves that the square of its
original exponential factor is the rational number `1/N` for every
positive finite cutoff.
[GaussianGammaHalfWallisRate](Lean/IPRADerivations/Analysis/GaussianGammaHalfWallisRate.lean) gives the finite Wallis rate to the exact arctangent
quadrature. [GaussianGammaHalfSquareLimit](Lean/IPRADerivations/Analysis/GaussianGammaHalfSquareLimit.lean) proves that the actual square of the original
half-Gamma name is the arctangent name for pi. [GaussianGammaHalfPositiveRoot](Lean/IPRADerivations/Analysis/GaussianGammaHalfPositiveRoot.lean) checks positivity
and the real axis for the same square root. [GaussianGammaHalfSqrtPi](Lean/IPRADerivations/Analysis/GaussianGammaHalfSqrtPi.lean)
identifies it with the independently evaluated dyadic square-root program.
[GaussianEulerBetaPrimitivePascal](Lean/IPRADerivations/Analysis/GaussianEulerBetaPrimitivePascal.lean)
proves the actual primitive coefficient recurrence at all degrees.
[GaussianEulerBetaEndpoint](Lean/IPRADerivations/Analysis/GaussianEulerBetaEndpoint.lean)
identifies the literal primitive at one with the original factorial
quotient for arbitrary internal degree under the native half-plane
guard.
[GaussianPositiveRationalLogarithmIncrement](Lean/IPRADerivations/Analysis/GaussianPositiveRationalLogarithmIncrement.lean)
checks the original positive-rational logarithm increment with its
quadratic remainder and independent observation errors.
[GaussianBetaKernelDomination](Lean/IPRADerivations/Analysis/GaussianBetaKernelDomination.lean)
gives nonnegativity and the original decay upper bound across the
entire finite support.
[GaussianRationalFirstOrderPolynomial](Lean/IPRADerivations/Analysis/GaussianRationalFirstOrderPolynomial.lean)
gives the actual beta primitive polynomial increment with a
quadratic residual. [GaussianRationalUniformFirstOrderPolynomial](Lean/IPRADerivations/Analysis/GaussianRationalUniformFirstOrderPolynomial.lean)
makes the polynomial estimate uniform on the compact disk.
[GaussianEulerPowerIncrement](Lean/IPRADerivations/Analysis/GaussianEulerPowerIncrement.lean)
checks the original power increment with the compact quadratic
remainder and the two requested observation errors.
[GaussianBetaPrimitiveCompactStep](Lean/IPRADerivations/Analysis/GaussianBetaPrimitiveCompactStep.lean)
uses the exact synthetic slope and the original power clock to compare
successive primitive samples to the actual weighted beta row.
[GaussianBetaPrimitiveGridTelescope](Lean/IPRADerivations/Analysis/GaussianBetaPrimitiveGridTelescope.lean)
checks the exact finite telescoping and sums that shape of cell error
on the original affine mesh.
[GaussianBetaPrimitiveCompactGridAccuracy](Lean/IPRADerivations/Analysis/GaussianBetaPrimitiveCompactGridAccuracy.lean)
discharges the local conditions from the native compact interval bounds
and computes the mesh and observation precision for any requested
dyadic error.
[GaussianBetaPrimitiveLowerEndpointRefinement](Lean/IPRADerivations/Analysis/GaussianBetaPrimitiveLowerEndpointRefinement.lean)
gives the vanishing degree-scaled lower endpoint at the actual grid
clock. [GaussianBetaUpperEndpointInverse](Lean/IPRADerivations/Analysis/GaussianBetaUpperEndpointInverse.lean)
identifies the literal degree-scaled upper endpoint name with the
original finite Euler reciprocal.
[GaussianBetaUpperGridEndpoint](Lean/IPRADerivations/Analysis/GaussianBetaUpperGridEndpoint.lean)
makes this comparison for the raw upper grid observation at the
original row clock, with two independent dyadic errors.
[GaussianBetaFiniteEulerComparison](Lean/IPRADerivations/Analysis/GaussianBetaFiniteEulerComparison.lean)
compares the unchanged beta quadrature on the whole interval from a
computed lower cutoff to the support endpoint with the original finite
Euler reciprocal at independently requested precisions. The positive
mesh and evaluation precision are computed and may be refined.
[GaussianBetaKernelCompactUpperTail](Lean/IPRADerivations/Analysis/GaussianBetaKernelCompactUpperTail.lean)
bounds the original upper beta quadrature through the support endpoint
using the existing half-decay estimates.
[GaussianBetaKernelLowerTransformedPower](Lean/IPRADerivations/Analysis/GaussianBetaKernelLowerTransformedPower.lean)
bounds the original lower transformed rows uniformly in the finite
degree.
[GaussianBetaKernelCompactModulus](Lean/IPRADerivations/Analysis/GaussianBetaKernelCompactModulus.lean)
proves the compact sampled modulus of that same evaluator uniformly in
the degree.
[GaussianBetaKernelLowerRootQuadrature](Lean/IPRADerivations/Analysis/GaussianBetaKernelLowerRootQuadrature.lean)
derives the original lower root-grid tail estimate uniformly in the degree.
[GaussianBetaFiniteEulerAtCutoff](Lean/IPRADerivations/Analysis/GaussianBetaFiniteEulerAtCutoff.lean)
uses the uniform beta primitive bound to let the lower cutoff be
chosen independently of the degree.
[GaussianBetaFixedCutoffSplit](Lean/IPRADerivations/Analysis/GaussianBetaFixedCutoffSplit.lean)
splits that grid into the actual compact middle and upper tail at the
same step.
[GaussianBetaRefinedFixedCompactBudget](Lean/IPRADerivations/Analysis/GaussianBetaRefinedFixedCompactBudget.lean)
computes the degree and evaluation precision for the actual middle
comparison at any requested dyadic error.
[GaussianEulerIntegralGammaIdentification](Lean/IPRADerivations/Analysis/GaussianEulerIntegralGammaIdentification.lean)
proves agreement of the original improper Euler and Gamma names, with
the two independent dyadic observation errors, for an arbitrary encoded
complex rational input on the positive real half-plane.
[GaussianNamedRightHalfPlane](Lean/IPRADerivations/Analysis/GaussianNamedRightHalfPlane.lean)
derives a native positive margin and a uniform disk for late observations
of a fixed regular input name.
[GaussianGammaHalfPlaneInputContinuity](Lean/IPRADerivations/Analysis/GaussianGammaHalfPlaneInputContinuity.lean)
proves a mixed-denominator modulus for the original Gamma observations.
[GaussianNamedGamma](Lean/IPRADerivations/Analysis/GaussianNamedGamma.lean)
uses that modulus to derive the regularity of the actual Gamma evaluator
on the fixed input name.
[GaussianNamedEulerIntegrand](Lean/IPRADerivations/Analysis/GaussianNamedEulerIntegrand.lean)
proves regularity of the actual integrand at every positive rational time
and agreement with the old integrand for equal encoded rational inputs.
[GaussianEulerIntegrandParameterContinuity](Lean/IPRADerivations/Analysis/GaussianEulerIntegrandParameterContinuity.lean)
bounds the compact variation between independently encoded rational
parameters at the same time.
[GaussianNamedEulerIntegrandParameterContinuity](Lean/IPRADerivations/Analysis/GaussianNamedEulerIntegrandParameterContinuity.lean)
carries the compact parameter comparison to a fixed complex name
and its frozen rational observation.
[GaussianNamedEulerCompactTimeRate](Lean/IPRADerivations/Analysis/GaussianNamedEulerCompactTimeRate.lean)
derives the compact time rate on the actual named evaluator.
[GaussianNamedEulerQuadrature](Lean/IPRADerivations/Analysis/GaussianNamedEulerQuadrature.lean)
evaluates that named integrand on the original varying grids with
the certified margin parameter `2A`. Advancing the outer precision by
three gives a regular improper integral name and proves agreement with
the original Gamma program on a fixed regular complex input at arbitrary
independent output precisions.
[GaussianNamedEulerCompactModulus](Lean/IPRADerivations/Analysis/GaussianNamedEulerCompactModulus.lean)
constructs the actual regular fixed compact quadrature from the sampled
modulus. [GaussianNamedEulerCutoffBinding](Lean/IPRADerivations/Analysis/GaussianNamedEulerCutoffBinding.lean)
identifies each varying-cutoff sample with the corresponding fixed
compact observation at the original clock. The literal C_R/N plus
exponential tail rate of the report remains.

## Every ledger family remains in scope

| Ledger IDs | Complete source deliverables still required |
| --- | --- |
| 1 | Actual harmonic/logarithm Euler-constant evaluator, C1–C2 inequalities, a regular name, and its bounds. |
| 2–3 | Actual cofinal samplers establish C11 for the literal Weierstrass product and C15 for the Euler reciprocals. The C7 and Gamma names agree on overlapping disks for the same encoded rational point. The right-half-plane Euler integral agrees with the original Gamma name on encoded complex rational inputs. The Gamma evaluator and fixed-time Euler integrand now extend to regular fixed complex names. The original improper Euler quadrature on a fixed regular complex name agrees with its Gamma name. |
| 4–10 | The original C7 zero predicate is characterized by an exact pole search for encoded rational inputs. The actual Gamma observations have a quantitative nonvanishing bound on pole-free disks. The whole finite coefficient product has the C9 majorant and the radius-doubled degree tail. C23 and C25 have checked difference-quotient and residue limits on encoded rational increments. The original cofinal coefficient names and C19 are checked on encoded disks. Entire analyticity and classification for general named inputs remain. C20, the original C21 shift and factorial values, C22, and the C24 punctured-disk identity are proved on their recorded domains. C26 conjugation and the real value representation for encoded real rational inputs are proved for the original reciprocal and pole-free Gamma names. |
| 11–17 | [GaussianGammaIntegralCutoffs](Lean/IPRADerivations/Analysis/GaussianGammaIntegralCutoffs.lean) checks the numerical endpoints and budgets for the original mesh. [GaussianPositiveRationalLogarithm](Lean/IPRADerivations/Analysis/GaussianPositiveRationalLogarithm.lean) constructs the positive-rational logarithm and checks its exponential. [GaussianPositiveExponentialTermBound](Lean/IPRADerivations/Analysis/GaussianPositiveExponentialTermBound.lean) checks the finite factorial-term lower bound used in the upper integral tail. [GaussianEulerIntegrandName](Lean/IPRADerivations/Analysis/GaussianEulerIntegrandName.lean) constructs the actual regular sampled integrand. [GaussianRationalRiemannRefinement](Lean/IPRADerivations/Analysis/GaussianRationalRiemannRefinement.lean) proves the weighted finite refinement bound from the original cell distances. [GaussianPositiveRationalExponentialDecay](Lean/IPRADerivations/Analysis/GaussianPositiveRationalExponentialDecay.lean) proves the factorial monomial bound for the named negative exponential with explicit dyadic observation slack. [GaussianEulerDecayFactorBounds](Lean/IPRADerivations/Analysis/GaussianEulerDecayFactorBounds.lean) transfers the dyadic integer and weighted half-argument bounds to the actual decay program. [GaussianGammaIntegralTailBudget](Lean/IPRADerivations/Analysis/GaussianGammaIntegralTailBudget.lean) checks the exact left root and the combined endpoint majorant at the prescribed cutoffs. [RationalHarmonicInterval](Lean/IPRADerivations/Analysis/RationalHarmonicInterval.lean) proves the exact signed harmonic-interval refinement and equal-ratio estimates. [GaussianExponentialLinearRemainder](Lean/IPRADerivations/Analysis/GaussianExponentialLinearRemainder.lean) checks the original exponential linear remainder on the unit disk. [GaussianPositiveRationalLogarithmProperness](Lean/IPRADerivations/Analysis/GaussianPositiveRationalLogarithmProperness.lean) proves agreement of the original logarithm across equal positive rational encodings. [GaussianGammaRightHalfPlane](Lean/IPRADerivations/Analysis/GaussianGammaRightHalfPlane.lean) derives the original Gamma domain and C15 rate from the positive real-part margin. [RationalHarmonicIntervalVariation](Lean/IPRADerivations/Analysis/RationalHarmonicIntervalVariation.lean) gives the finite harmonic variation bound and [GaussianNamedLipschitzRate](Lean/IPRADerivations/Analysis/GaussianNamedLipschitzRate.lean) removes auxiliary dyadic errors from diagonal estimates of regular names. [GaussianCompactRiemannName](Lean/IPRADerivations/Analysis/GaussianCompactRiemannName.lean) derives regular compact quadrature from an actual local sampled modulus. [GaussianGammaCompactQuadratureBoundary](Lean/IPRADerivations/Analysis/GaussianGammaCompactQuadratureBoundary.lean) binds that construction to the Gamma cutoffs on each fixed interval. [GaussianEulerDecayAddition](Lean/IPRADerivations/Analysis/GaussianEulerDecayAddition.lean) checks addition of rational decay arguments and the linear remainder for the original decay samples. [GaussianPositiveRationalLogarithmVariation](Lean/IPRADerivations/Analysis/GaussianPositiveRationalLogarithmVariation.lean) proves the original logarithm variation rate. [GaussianRationalUniformExponentialLipschitz](Lean/IPRADerivations/Analysis/GaussianRationalUniformExponentialLipschitz.lean) gives a uniform variation bound for the original finite scalar exponential on a disk. [GaussianEulerDecayIncrement](Lean/IPRADerivations/Analysis/GaussianEulerDecayIncrement.lean) establishes a uniform first-order remainder for the original positive-time decay samples. [GaussianEulerDecayMesh](Lean/IPRADerivations/Analysis/GaussianEulerDecayMesh.lean) sums this error on an actual finite mesh and compares to the endpoint difference. [GaussianEulerDecayQuadrature](Lean/IPRADerivations/Analysis/GaussianEulerDecayQuadrature.lean) compares the actual affine-grid decay sum to the two original endpoint observations with a quantitative error. [GaussianCompactLogarithmBounds](Lean/IPRADerivations/Analysis/GaussianCompactLogarithmBounds.lean) bounds the actual compact logarithm observations uniformly. [GaussianRadiusExponentialLipschitzRate](Lean/IPRADerivations/Analysis/GaussianRadiusExponentialLipschitzRate.lean) lifts the finite variation bound to the original exponential names. [GaussianPositiveExponentialOrder](Lean/IPRADerivations/Analysis/GaussianPositiveExponentialOrder.lean) checks finite positive-axis order and [GaussianExponentialRealPart](Lean/IPRADerivations/Analysis/GaussianExponentialRealPart.lean) relates the exponential norm square to the real part of its exponent. The [checked Euler quadrature](#checked-euler-quadrature) now supplies the original integrand modulus, regular varying-endpoint improper quadrature, and its comparison to each fixed compact name with both endpoint majorants. The Euler-integral identification is checked on encoded rationals and fixed regular complex names. The sharp finite Euler rate is checked for every degree at least two on encoded complex inputs. The stated degree schedule gives the evaluated original observation corollaries. The sharp finite-sampler rate extends to general regular complex names at the computed radius. The one-eighteenth lower bound is checked for encoded positive real inputs and regular positive real names with actual real samples. The combined factorial upper bound is checked on encoded inputs and regular names at their computed radii. The decay antiderivative gives a checked integral proof of the Gamma value at one. The vertical integrand squared norm identity is checked. The vertical Gamma comparison is checked for encoded inputs and regular complex names. Integration by parts gives the recurrence on encoded rational inputs and regular complex names. The compact logarithmic quadratures, incomplete-Gamma sum and both recurrences are checked on encoded rational inputs with positive rational split. The upper and lower integer formulas are checked for all numerical indices at positive rational splits. Every positive rational split at most the original cutoff has the exact root rate to the zero-split values. The all-order derivative of the logarithmic integral names (family 14) is checked on certified native Gaussian rationals and fixed regular complex input names, including named increments with finite apartness and all-observation smallness. The finite Euler scaling comparison includes the exact Jacobian. Its cofinal lift proves the improper scaling law at exponent parameter one for positive rational damping and encoded complex input, including the direct original Gamma identity. The quadratic map has checked finite Jacobian and complex-power identities, actual pointwise integrand transport, compact Jacobian-weighted integration on positive-width rational intervals, and both omitted tails. Its cofinal lift proves the quadratic improper identity with the original Gamma evaluator for positive rational damping and encoded complex input. The exponential improper form is checked on the actual ordered logarithmic image partitions with explicit cofinal endpoint bounds. The unit-interval decay-image sampler is checked against the original Gamma evaluator, with explicit endpoint exhaustion and shrinking mesh. The genuine unit kernel has a uniform compact rate, a checked extension to regular compact real input names, and a checked pointwise pullback to the original Euler power at every certified decay-image input. The finite density is compared with independently counted uniform quadratures on the rounded rational panels. The original Gamma name is identified with the cofinal ordinary quadrature on the computed rational unit panels, with an independently later original time cutoff and explicit endpoint exhaustion. Compact endpoint continuity holds at independent rational denominators and observation indices, and arbitrary fixed proper rational panels are eventually contained in the computed cofinal panels. Exact nested panel splitting and compact real-parameter domination are checked at independent observation indices. A uniform omitted-tail bound identifies arbitrary proper rational endpoint exhaustions with the original Gamma name for encoded complex inputs, with independent observation queries. [GaussianEulerPowerScalingImproper](Lean/IPRADerivations/Analysis/GaussianEulerPowerScalingImproper.lean) proves the original improper power-damping identity for positive rational damping and exponent and encoded complex input. The extension to arbitrary positive real scaling remains open. |
| 18–24 | Reflection with an explicit sine margin, multiplication at arbitrary internal positive integer multiplier, duplication/triplication, beta–Gamma relation, beta symmetry/recurrence and all stated integral forms with their positive half-plane margins. [GaussianScalarExponentialOddTaylor](Lean/IPRADerivations/Analysis/GaussianScalarExponentialOddTaylor.lean), [GaussianScalarSineTaylor](Lean/IPRADerivations/Analysis/GaussianScalarSineTaylor.lean), and [GaussianNamedSineTaylor](Lean/IPRADerivations/Analysis/GaussianNamedSineTaylor.lean) give the finite and named sine series identities used in the trigonometric foundation. [GaussianArctangentCayleyRefinement](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyRefinement.lean) proves the explicit finite Cayley estimate at any rational arctangent endpoint in the unit interval. [GaussianArctangentPartialQuadrature](Lean/IPRADerivations/Analysis/GaussianArctangentPartialQuadrature.lean) gives the regular native partial arctangent, [GaussianArctangentPartialRepresentation](Lean/IPRADerivations/Analysis/GaussianArctangentPartialRepresentation.lean) removes dependence on the fraction encoding, and [GaussianArctangentPartialUnitEndpoint](Lean/IPRADerivations/Analysis/GaussianArctangentPartialUnitEndpoint.lean) matches the unit endpoint with the original π program. [GaussianArctangentPartialExponential](Lean/IPRADerivations/Analysis/GaussianArctangentPartialExponential.lean) and [GaussianArctangentPartialTrig](Lean/IPRADerivations/Analysis/GaussianArctangentPartialTrig.lean) prove the named exponential, sine and cosine identities in T1 at every encoded rational arctangent parameter in the unit interval. [GaussianArctangentChordComparison](Lean/IPRADerivations/Analysis/GaussianArctangentChordComparison.lean) and [GaussianArctangentNamedChord](Lean/IPRADerivations/Analysis/GaussianArctangentNamedChord.lean) give the finite and independently sampled T2 chord comparison on the rational arctangent image. [GaussianArctangentSlope](Lean/IPRADerivations/Analysis/GaussianArctangentSlope.lean) proves the finite lower and upper slope bounds, and [GaussianArctangentGridSearch](Lean/IPRADerivations/Analysis/GaussianArctangentGridSearch.lean) finds the first row crossing a target with an explicit residual. [GaussianArctangentNamedSlope](Lean/IPRADerivations/Analysis/GaussianArctangentNamedSlope.lean) lifts the two slope bounds to the original names at independent precisions. [GaussianArctangentRationalTarget](Lean/IPRADerivations/Analysis/GaussianArctangentRationalTarget.lean) clears rational target denominators exactly and bounds the selected observation by `2/M` from the target when it is in the finite grid range. [GaussianArctangentClampedTarget](Lean/IPRADerivations/Analysis/GaussianArctangentClampedTarget.lean) proves the native prefix is independent of the clearing factorial and verifies clipping to the endpoints for finite nonnegative inverse targets. [GaussianArctangentPhysicalRefinement](Lean/IPRADerivations/Analysis/GaussianArctangentPhysicalRefinement.lean) retains the actual mesh denominator in the forward error and compares any selected inverse sample to the original named arctangent at the selected rational parameter. [GaussianArctangentInverseSampler](Lean/IPRADerivations/Analysis/GaussianArctangentInverseSampler.lean) and [GaussianArctangentInverseForward](Lean/IPRADerivations/Analysis/GaussianArctangentInverseForward.lean) implement the inverse sampler for arbitrary regular angles certified by the independent-precision interval inequalities, with forward error at most `7/2^p` on the selected finite grid. [GaussianArctangentInverseGap](Lean/IPRADerivations/Analysis/GaussianArctangentInverseGap.lean) transfers forward errors to rational parameter errors. [GaussianArctangentNamedInverse](Lean/IPRADerivations/Analysis/GaussianArctangentNamedInverse.lean) proves regularity and exact rational readback for the inverse. [GaussianArctangentInverseUniqueness](Lean/IPRADerivations/Analysis/GaussianArctangentInverseUniqueness.lean) proves equivalence for inverse names of equivalent target angles, and [GaussianImaginaryCoordinateName](Lean/IPRADerivations/Analysis/GaussianImaginaryCoordinateName.lean) checks the regular coordinate name used to state the inverse identity. [GaussianArctangentNamedExtension](Lean/IPRADerivations/Analysis/GaussianArctangentNamedExtension.lean) defines the regular forward name and [GaussianArctangentExtensionRange](Lean/IPRADerivations/Analysis/GaussianArctangentExtensionRange.lean) certifies its target interval. [GaussianArctangentInverseCorrectness](Lean/IPRADerivations/Analysis/GaussianArctangentInverseCorrectness.lean) identifies the angle coordinate after forward evaluation of the inverse and gives full Gaussian name equivalence for imaginary-axis angle samples. [GaussianArctangentNamedExtensionUniqueness](Lean/IPRADerivations/Analysis/GaussianArctangentNamedExtensionUniqueness.lean) recovers exactly represented unit-interval parameter names after the opposite round trip. [GaussianArctangentNamedCayley](Lean/IPRADerivations/Analysis/GaussianArctangentNamedCayley.lean) identifies the original named exponential of the general forward program with regular observations of the literal Cayley quotient. [GaussianArctangentNamedCayleyTrig](Lean/IPRADerivations/Analysis/GaussianArctangentNamedCayleyTrig.lean) identifies both original sine and cosine names with literal Cayley formulas on regular parameters. [GaussianArctangentNamedChordExtension](Lean/IPRADerivations/Analysis/GaussianArctangentNamedChordExtension.lean) proves the sampled chord for the general forward name, and [GaussianArctangentAngleChord](Lean/IPRADerivations/Analysis/GaussianArctangentAngleChord.lean) transfers it through the exact inverse to every certified imaginary-axis angle in the original interval. [GaussianArctangentPiMargins](Lean/IPRADerivations/Analysis/GaussianArctangentPiMargins.lean) proves the margins 1501/500 ≤ π ≤ 7/2 with the observation error. For T3, [GaussianScalarSincTaylor](Lean/IPRADerivations/Analysis/GaussianScalarSincTaylor.lean) proves the literal finite sine–sinc identity at all inputs, [GaussianScalarSincTaylorBounds](Lean/IPRADerivations/Analysis/GaussianScalarSincTaylorBounds.lean) gives the quadratic error on the unit disk, and [GaussianSineMultipleAngleRecurrence](Lean/IPRADerivations/Analysis/GaussianSineMultipleAngleRecurrence.lean) proves the zero-safe multiple-angle difference law and even recurrence. [GaussianNamedSinc](Lean/IPRADerivations/Analysis/GaussianNamedSinc.lean) constructs the regular factorial sinc name on bounded inputs and [GaussianNamedSineSincFactorization](Lean/IPRADerivations/Analysis/GaussianNamedSineSincFactorization.lean) proves its division-free identity with the original named sine. [GaussianSineSquaredPolynomial](Lean/IPRADerivations/Analysis/GaussianSineSquaredPolynomial.lean) gives the actual monic multiple-angle polynomial; [GaussianSineSquaredTrace](Lean/IPRADerivations/Analysis/GaussianSineSquaredTrace.lean) evaluates it at the squared-sine coordinate and proves the rational power-difference root implication; [GaussianSineSquaredNormalization](Lean/IPRADerivations/Analysis/GaussianSineSquaredNormalization.lean) evaluates it at zero sine. [GaussianArctangentDivisionAngles](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionAngles.lean) certifies the divided angles, and [GaussianArctangentDivisionAngleRoots](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionAngleRoots.lean) proves the original sine vanishes after multiplication by the odd order. [GaussianArctangentDivisionAngleGaps](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionAngleGaps.lean) proves the uniform synchronized gaps between the angle observations and from the quarter endpoint. [GaussianRationalSeparatedDeflation](Lean/IPRADerivations/Analysis/GaussianRationalSeparatedDeflation.lean) propagates residual bounds through rational synthetic deflation, and [GaussianRationalSeparatedReconstruction](Lean/IPRADerivations/Analysis/GaussianRationalSeparatedReconstruction.lean) bounds the resulting product evaluation error at separated samples. [GaussianArctangentDivisionSinePositive](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionSinePositive.lean) proves the actual sine at each positive prescribed angle is at least 2k/m. [GaussianNamedSincQuadraticBounds](Lean/IPRADerivations/Analysis/GaussianNamedSincQuadraticBounds.lean) and [GaussianNamedSincRatio](Lean/IPRADerivations/Analysis/GaussianNamedSincRatio.lean) give the original named sinc quadratic and squared-ratio estimates. [GaussianInverseSquareProductTail](Lean/IPRADerivations/Analysis/GaussianInverseSquareProductTail.lean) proves an explicit finite inverse-square product tail and [GaussianSineProductName](Lean/IPRADerivations/Analysis/GaussianSineProductName.lean) gives a regular name for the literal product. [GaussianSineProductT4Budget](Lean/IPRADerivations/Analysis/GaussianSineProductT4Budget.lean) checks the numerical T4 clock and closes the final error absorption under its product and prefactor estimates. For R1, [GaussianGammaEulerReflectionHead](Lean/IPRADerivations/Analysis/GaussianGammaEulerReflectionHead.lean) pairs the original heads and [GaussianGammaEulerReflectionName](Lean/IPRADerivations/Analysis/GaussianGammaEulerReflectionName.lean) proves the exact reflection value of the original finite Euler approximant names on the certified pole-free domain. [GaussianGammaEulerReflectionLimit](Lean/IPRADerivations/Analysis/GaussianGammaEulerReflectionLimit.lean) passes the finite identity to the original reciprocal Gamma names at independent output precisions. [GaussianGammaReflectionProduct](Lean/IPRADerivations/Analysis/GaussianGammaReflectionProduct.lean) proves the limiting reflection product for the original Gamma names at $z$ and $1-z$, with constructive division by $zS(z)$ on the certified pole-free domain. [GaussianGammaReflectionSineTransfer](Lean/IPRADerivations/Analysis/GaussianGammaReflectionSineTransfer.lean) derives the original cleared sine reflection formula from T7 at the original argument. [GaussianInverseSquareProductGrowth](Lean/IPRADerivations/Analysis/GaussianInverseSquareProductGrowth.lean) checks the uniform inverse-square product envelope, [GaussianArctangentCayleySquareGap](Lean/IPRADerivations/Analysis/GaussianArctangentCayleySquareGap.lean) gives the finite Cayley square gap, and [GaussianSineSquaredResidual](Lean/IPRADerivations/Analysis/GaussianSineSquaredResidual.lean) converts the power discrepancy into a quantitative polynomial residual. [GaussianArctangentDivisionAngleResidual](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionAngleResidual.lean) bounds the residual at the actual rational Cayley observations given a sampled sine margin. [GaussianInverseSquareProductComparison](Lean/IPRADerivations/Analysis/GaussianInverseSquareProductComparison.lean) bounds the weighted difference of the actual finite products. [GaussianSineSampleRootList](Lean/IPRADerivations/Analysis/GaussianSineSampleRootList.lean) instantiates the finite monic reconstruction bound with the original rational root samples under explicit separation. [GaussianArctangentDivisionCayleyMargins](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionCayleyMargins.lean) proves the sampled sine lower bounds and pairwise squared-sine separation on the actual inverse grid. [GaussianSineProductT6](Lean/IPRADerivations/Analysis/GaussianSineProductT6.lean) combines the finite head, suffix, and sinc prefactor estimates to the exact T4 radius, and [GaussianSineProductT4Finite](Lean/IPRADerivations/Analysis/GaussianSineProductT4Finite.lean) closes the finite quantified estimate and dyadic precision form. [GaussianSincRatioProductRow](Lean/IPRADerivations/Analysis/GaussianSincRatioProductRow.lean) derives the head and prefactor estimates from certified sinc observations. [GaussianSineRootNormalization](Lean/IPRADerivations/Analysis/GaussianSineRootNormalization.lean) identifies each normalized linear root factor with $1-s^2/r^2$ under its proved sine margin. [GaussianSineSampleRootGuards](Lean/IPRADerivations/Analysis/GaussianSineSampleRootGuards.lean) applies the exact rational root margin and residual estimates to the actual polynomial and its finite root list. [GaussianSineSquaredRootSeparation](Lean/IPRADerivations/Analysis/GaussianSineSquaredRootSeparation.lean) applies the exact rational root margin and residual estimates to the actual polynomial and its finite root list. [GaussianArctangentDivisionSineSeparation](Lean/IPRADerivations/Analysis/GaussianArctangentDivisionSineSeparation.lean) transfers the gap to the original squared sine names at independent precisions, and [GaussianSineProductScaledArguments](Lean/IPRADerivations/Analysis/GaussianSineProductScaledArguments.lean) checks the actual T4 scaled arguments and their sinc radius guards. [GaussianSineNormalizedSampleProduct](Lean/IPRADerivations/Analysis/GaussianSineNormalizedSampleProduct.lean) proves the exact normalized finite factor fold, and [GaussianSineNormalizedSampleReconstruction](Lean/IPRADerivations/Analysis/GaussianSineNormalizedSampleReconstruction.lean) gives an explicit cofinal error against the multiple-angle polynomial divided by the odd order. [GaussianNamedSineMultipleAngle](Lean/IPRADerivations/Analysis/GaussianNamedSineMultipleAngle.lean) proves the named multiple-angle sine identity on every bounded Gaussian input, and [GaussianNamedEvenSinePolynomial](Lean/IPRADerivations/Analysis/GaussianNamedEvenSinePolynomial.lean) identifies its even recurrence with the odd order times the normalized polynomial. [GaussianSineNormalizedSampleName](Lean/IPRADerivations/Analysis/GaussianSineNormalizedSampleName.lean) identifies the normalized polynomial with the regular root-product name. [GaussianSineNormalizedForwardProduct](Lean/IPRADerivations/Analysis/GaussianSineNormalizedForwardProduct.lean) verifies the ascending rational factor order. [GaussianSineProductScaledArgumentIdentity](Lean/IPRADerivations/Analysis/GaussianSineProductScaledArgumentIdentity.lean) and [GaussianSineProductRelativeArgument](Lean/IPRADerivations/Analysis/GaussianSineProductRelativeArgument.lean) bind the original scaled arguments and root sine to the literal arithmetic. For R3, [GaussianSineProductHeadLower](Lean/IPRADerivations/Analysis/GaussianSineProductHeadLower.lean) and [GaussianSineProductTailLower](Lean/IPRADerivations/Analysis/GaussianSineProductTailLower.lean) prove the factorial head and inverse-square tail bounds, [GaussianSineProductReflectionLower](Lean/IPRADerivations/Analysis/GaussianSineProductReflectionLower.lean) transfers their exact product to the original name, and [GaussianSineReflectionLower](Lean/IPRADerivations/Analysis/GaussianSineReflectionLower.lean) proves the original sine lower bound at an explicit dyadic reserve given the T7 identity. [GaussianNamedSincCongruence](Lean/IPRADerivations/Analysis/GaussianNamedSincCongruence.lean) transports sinc across independently certified equivalent names. [GaussianSineProductNamedT3](Lean/IPRADerivations/Analysis/GaussianSineProductNamedT3.lean) proves T3 at the original reflection argument, with explicit cancellation for nonzero numerators and exact zero-sample identities at zero. [GaussianSineRawRootBinding](Lean/IPRADerivations/Analysis/GaussianSineRawRootBinding.lean) and [GaussianSineProductSynchronizedRow](Lean/IPRADerivations/Analysis/GaussianSineProductSynchronizedRow.lean) identify the original Cayley observations and bound each actual normalized factor at a synchronized query clock. [GaussianSineProductSynchronizedMagnitude](Lean/IPRADerivations/Analysis/GaussianSineProductSynchronizedMagnitude.lean) verifies the inverse-square envelope on all actual Cayley rows. [GaussianSineProductT4Actual](Lean/IPRADerivations/Analysis/GaussianSineProductT4Actual.lean) proves the synchronized comparisons at the common cofinal clock, and [GaussianSineProductT7Actual](Lean/IPRADerivations/Analysis/GaussianSineProductT7Actual.lean) proves the T7 identity for the original sinc, the exact R3 bound at every certified precision, and both cleared and divided Gamma reflection (claim 18). The ordinary quotient uses [GaussianGammaReflectionQuotient](Lean/IPRADerivations/Analysis/GaussianGammaReflectionQuotient.lean) and [GaussianGammaReflectionR3Domain](Lean/IPRADerivations/Analysis/GaussianGammaReflectionR3Domain.lean) to compute the sine reciprocal from the original complementary pole guards. For Gauss multiplication, [GaussianRationalRectangularProduct](Lean/IPRADerivations/Analysis/GaussianRationalRectangularProduct.lean), [GaussianGammaEulerDenominator](Lean/IPRADerivations/Analysis/GaussianGammaEulerDenominator.lean), and [GaussianGammaEulerDenominatorGrouping](Lean/IPRADerivations/Analysis/GaussianGammaEulerDenominatorGrouping.lean) prove the finite denominator grouping in M2 at arbitrary positive integer multiplier. [GaussianGammaGaussEulerHeads](Lean/IPRADerivations/Analysis/GaussianGammaGaussEulerHeads.lean) identifies the grouped product of the actual shifted Euler heads with the factorial-normalized head at the Gauss cutoff. [GaussianGammaGaussDomain](Lean/IPRADerivations/Analysis/GaussianGammaGaussDomain.lean) pulls the original scaled pole guard back to every shifted argument. [GaussianGammaGaussReference](Lean/IPRADerivations/Analysis/GaussianGammaGaussReference.lean) certifies the positive normalization arguments and computes the common exponent offsets. For M1, [GaussianCyclicExponentialRoots](Lean/IPRADerivations/Analysis/GaussianCyclicExponentialRoots.lean) proves the original cyclic root law and [GaussianCyclicExponentialSeparation](Lean/IPRADerivations/Analysis/GaussianCyclicExponentialSeparation.lean) supplies separated actual observations. For M3, [GaussianGaussMultiplicationLogarithm](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationLogarithm.lean) proves the exact $1/N$ bound on the original integer logarithm samples and gives an independent-clock version. [GaussianNamedFiniteProductName](Lean/IPRADerivations/Analysis/GaussianNamedFiniteProductName.lean) lifts rowwise approximations to the regular name of their finite product. [GaussianCyclicRootProduct](Lean/IPRADerivations/Analysis/GaussianCyclicRootProduct.lean) reconstructs the finite cofinal product of the nontrivial cyclic factors at one. [GaussianGaussEulerHeadCancellation](Lean/IPRADerivations/Analysis/GaussianGaussEulerHeadCancellation.lean) cancels the common factorial factors across two original Euler head products, and [GaussianGaussEulerRowExponents](Lean/IPRADerivations/Analysis/GaussianGaussEulerRowExponents.lean) identifies the common exponential factor for every shifted row. [GaussianGaussMultiplicationLogRatio](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationLogRatio.lean) proves the corresponding rate for the original positive rational log names at bases $N/L$ and $1/m$. [GaussianNamedFiniteProductApartness](Lean/IPRADerivations/Analysis/GaussianNamedFiniteProductApartness.lean) gives explicit reciprocal clocks for regular finite products with a uniform row margin, including the exact empty product. [GaussianGaussMultiplicationSharpPowerRate](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationSharpPowerRate.lean) proves M3 with exact leading coefficient $2A m^A$, where $A=m(R+1)$, and the independent observation errors. [GaussianGaussEulerCutoff](Lean/IPRADerivations/Analysis/GaussianGaussEulerCutoff.lean) computes the common Euler cutoff and proves that each larger cutoff also gives the required error. [GaussianGammaGaussShiftedProduct](Lean/IPRADerivations/Analysis/GaussianGammaGaussShiftedProduct.lean), [GaussianGammaGaussShiftedApartness](Lean/IPRADerivations/Analysis/GaussianGammaGaussShiftedApartness.lean), and [GaussianGammaGaussEulerProduct](Lean/IPRADerivations/Analysis/GaussianGammaGaussEulerProduct.lean) construct the original shifted Gamma product, certify its reciprocal clock, and prove convergence of the literal finite Euler product. [GaussianNamedFiniteProductAlgebra](Lean/IPRADerivations/Analysis/GaussianNamedFiniteProductAlgebra.lean) and [GaussianNamedRepeatedExponential](Lean/IPRADerivations/Analysis/GaussianNamedRepeatedExponential.lean) transport finite rowwise multiplication and repeated exponentials through the actual clocks. [GaussianCyclicChordSquare](Lean/IPRADerivations/Analysis/GaussianCyclicChordSquare.lean) and [GaussianCyclicSineProductSquare](Lean/IPRADerivations/Analysis/GaussianCyclicSineProductSquare.lean) identify the cyclic chord product with the squared sine product at certified clocks. [GaussianCyclicSinePositiveRows](Lean/IPRADerivations/Analysis/GaussianCyclicSinePositiveRows.lean) and [GaussianCyclicSineProductNormalization](Lean/IPRADerivations/Analysis/GaussianCyclicSineProductNormalization.lean) justify cancellation of the square on the actual finite rows. [GaussianCyclicSineProductName](Lean/IPRADerivations/Analysis/GaussianCyclicSineProductName.lean) proves M1 for the primitive recursive product of the original sine names at arbitrary positive internal order, with value $m/2^{m-1}$. [GaussianGaussEulerPowerRatio](Lean/IPRADerivations/Analysis/GaussianGaussEulerPowerRatio.lean) proves the exact ratio-power law at the two original cutoff logarithms, and [GaussianGaussEulerOffsetPower](Lean/IPRADerivations/Analysis/GaussianGaussEulerOffsetPower.lean) collects the repeated relative factors into the exponential of the scaled coefficient. [GaussianGammaEulerFullHeadInverse](Lean/IPRADerivations/Analysis/GaussianGammaEulerFullHeadInverse.lean) factors each actual Euler name through its complete head reciprocal. [GaussianNamedFiniteProductFamilyCongruence](Lean/IPRADerivations/Analysis/GaussianNamedFiniteProductFamilyCongruence.lean) transports regular families of independently sampled rows to their actual product names. [GaussianGammaGaussReferenceProduct](Lean/IPRADerivations/Analysis/GaussianGammaGaussReferenceProduct.lean), [GaussianGammaGaussReferenceEulerProduct](Lean/IPRADerivations/Analysis/GaussianGammaGaussReferenceEulerProduct.lean), and [GaussianGaussMultiplicationCofinalRows](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationCofinalRows.lean) construct the reference product with a reciprocal clock and bind the shifted, reference, scaled, and ratio observations to their limiting names at one padded cutoff. [GaussianGaussMultiplicationM2Transport](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationM2Transport.lean) proves M4 in its cleared form from the exact named M2 identity at the cofinal Euler cutoffs. It constructs the named finite factors and uses uniform observation bounds to pass to the original Gamma names. [GaussianGaussEulerFiniteIdentity](Lean/IPRADerivations/Analysis/GaussianGaussEulerFiniteIdentity.lean) proves exact cleared M2 on the original finite Euler names and passes to the cleared Gamma limit at the cofinal cutoffs. [GaussianGammaGaussReferenceSquare](Lean/IPRADerivations/Analysis/GaussianGammaGaussReferenceSquare.lean) proves the exact squared M5 normalization $P_m^2=(2\pi)^{m-1}/m$ for the original reference product, by the actual reflection rows and M1. [GaussianGammaGaussPositiveReference](Lean/IPRADerivations/Analysis/GaussianGammaGaussPositiveReference.lean) gives a primitive recursive representative of the certified positive root and proves its real positivity and exact square. [GaussianGaussMultiplication](Lean/IPRADerivations/Analysis/GaussianGaussMultiplication.lean) proves the divided M4 formula with the actual scaled Gamma reciprocal and the M5 formula in the form $m^{1-mz}\sqrt{(2\pi)^{m-1}/m}\,\Gamma(mz)$ for every positive internal order. The normalized formula uses the certified positive-root representative from the reference rows. [GaussianGaussMultiplicationIndependentNormalization](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationIndependentNormalization.lean) also computes that root directly from the radicand. [GaussianGaussEulerRelativeQuotient](Lean/IPRADerivations/Analysis/GaussianGaussEulerRelativeQuotient.lean) proves the literal M2 nested quotient at every certified cutoff. [GaussianGaussMultiplicationHalfPowers](Lean/IPRADerivations/Analysis/GaussianGaussMultiplicationHalfPowers.lean) proves the displayed M5 identity with separately computed $(2\pi)^{(m-1)/2}$ and $m^{1/2-mz}$. [GaussianGaussDuplication](Lean/IPRADerivations/Analysis/GaussianGaussDuplication.lean) and [GaussianGaussTriplication](Lean/IPRADerivations/Analysis/GaussianGaussTriplication.lean) prove M6 and M7 for the explicit original Gamma rows at their common denominators. |
| 25–30 | Positive-root selection and half-integer values, the listed fractional-argument relations and fractional products, and imaginary/half-shifted modulus formulas, including their zero-safe versions. V8 and V9 hold for the original Gamma names on certified endpoints at arbitrary internal indices. The entire cleared V9 identity covers apparent cancelled poles. |
| 31–36 | Digamma and polygamma evaluators with remainder bounds, recurrences/signs/special derivative values, differentiated reflection/multiplication, rational-argument values, and the finite polynomial recursion for Gamma derivatives. Derivative orders may remain external where the source explicitly allows that schema. The original first derivative at one is identified with the negative Euler–Mascheroni name. [GaussianGammaDigammaNative](Lean/IPRADerivations/Analysis/GaussianGammaDigammaNative.lean) constructs the original positive rational digamma as $Γ'/Γ$, verifies the product with the original Gamma name, and proves $ψ(1)=-γ$. [GaussianGammaDigammaStep](Lean/IPRADerivations/Analysis/GaussianGammaDigammaStep.lean) binds the original derivative rate to literal rational increments $1/D$. [GaussianGammaDigammaDerivativeShift](Lean/IPRADerivations/Analysis/GaussianGammaDigammaDerivativeShift.lean) derives the differentiated Gamma recurrence and [GaussianGammaDigammaRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaDigammaRecurrence.lean) proves $ψ(x+1)=ψ(x)+1/x$ at every encoded positive rational point. [GaussianGammaDigammaInteger](Lean/IPRADerivations/Analysis/GaussianGammaDigammaInteger.lean) proves $ψ(n+1)=H_n-γ$ with an explicit independent-observation bound. [GaussianGammaDigammaFiniteSum](Lean/IPRADerivations/Analysis/GaussianGammaDigammaFiniteSum.lean) proves the finite reciprocal-sum formula for every internal natural shift of the original positive rational digamma. [GaussianGammaDigammaGammaComparison](Lean/IPRADerivations/Analysis/GaussianGammaDigammaGammaComparison.lean) proves the symmetric product inequality for original Gamma at a positive rational increment. [GaussianGammaDigammaMonotone](Lean/IPRADerivations/Analysis/GaussianGammaDigammaMonotone.lean) passes the verified derivative rates through the comparison and cancels positive Gamma factors to prove monotonicity of the original digamma. [GaussianGammaDigammaSeries](Lean/IPRADerivations/Analysis/GaussianGammaDigammaSeries.lean) proves the cofinal C28 rate for all encoded positive rational inputs, and [GaussianGammaDigammaSeriesTerms](Lean/IPRADerivations/Analysis/GaussianGammaDigammaSeriesTerms.lean) binds the finite correction to the literal reciprocal differences of the paper. [GaussianGammaDigammaPositiveTerms](Lean/IPRADerivations/Analysis/GaussianGammaDigammaPositiveTerms.lean) proves the original positive-term C27 representation, and [GaussianGammaDigammaEulerDerivative](Lean/IPRADerivations/Analysis/GaussianGammaDigammaEulerDerivative.lean) bounds the literal finite Euler slope against the original digamma with independent observation clocks. [GaussianGammaDigammaElementaryBounds](Lean/IPRADerivations/Analysis/GaussianGammaDigammaElementaryBounds.lean) and [GaussianGammaDigammaElementaryOriginalLog](Lean/IPRADerivations/Analysis/GaussianGammaDigammaElementaryOriginalLog.lean) prove the elementary logarithmic bracket on the original positive rational digamma with either original logarithm presentation. The polygamma and differentiated identity claims remain open. |
| 37–42 | [GaussianGammaCanonicalCoefficientRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalCoefficientRecurrence.lean) proves the C42 equality of the actual regular canonical coefficient and finite sum names. [GaussianGammaCanonicalRecurrenceZetaFormula](Lean/IPRADerivations/Analysis/GaussianGammaCanonicalRecurrenceZetaFormula.lean) identifies the right name with the original gamma and signed zeta formula at the same observations. The remaining local Taylor/log-Gamma expansions, Laurent constants and remainders at each pole, positive-integer-centered expansions, vertical modulus products, and balanced parameter products still require their named coefficient and discarded-tail comparisons. |
| 43–48 | Quantitative strict convexity, effective Bohr–Mollerup uniqueness at fixed presentations, Wendel/Gautschi inequalities, rate-bearing Gamma ratios, actual positive-minimum location and negative-pole interval extremum/sign constructions. [GaussianGammaEulerRationalHeadConvexity](Lean/IPRADerivations/Analysis/GaussianGammaEulerRationalHeadConvexity.lean) proves the weighted powered comparison on the original positive rational finite Euler heads. [GaussianGammaEulerRationalLogConvexity](Lean/IPRADerivations/Analysis/GaussianGammaEulerRationalLogConvexity.lean) proves exact weighted convexity on the original finite Euler logarithms. [GaussianNamedPositiveLogarithmRate](Lean/IPRADerivations/Analysis/GaussianNamedPositiveLogarithmRate.lean) proves quantitative transport through the named logarithm at a common positive lower bound. [GaussianGammaEulerRationalLogConvergence](Lean/IPRADerivations/Analysis/GaussianGammaEulerRationalLogConvergence.lean) proves the quantitative log convergence using the explicit cofinal positive margin. [GaussianGammaNativeLogConvexity](Lean/IPRADerivations/Analysis/GaussianGammaNativeLogConvexity.lean) passes the exact weighted convexity inequality to the native log-Gamma names on all encoded positive rational arguments. [GaussianGammaNativeMidpointLogGap](Lean/IPRADerivations/Analysis/GaussianGammaNativeMidpointLogGap.lean) adds the explicit margin $(a-d)^2/(a+d)^2$ to twice the native log-Gamma at the midpoint for positive rational endpoints $a/b$ and $d/b$. [GaussianGammaNativeWeightedLogGap](Lean/IPRADerivations/Analysis/GaussianGammaNativeWeightedLogGap.lean) extends this explicit margin to the sums with arbitrary positive natural weights. [GaussianGammaNativeStrictLogConvexity](Lean/IPRADerivations/Analysis/GaussianGammaNativeStrictLogConvexity.lean) proves strict log-convexity on distinct encoded positive rationals by negating reverse order. [GaussianGammaNativeStrongLogConvexity](Lean/IPRADerivations/Analysis/GaussianGammaNativeStrongLogConvexity.lean) proves the full weight-dependent modulus from the paper, with additive margin $rs(d-a)^2/(2(r+s)B^2)$ in the unnormalized comparison at $a/b,d/b$ with upper endpoint bound $B/b$ and natural weights $r>0,s\ge0$. [GaussianGammaRationalGautschi](Lean/IPRADerivations/Analysis/GaussianGammaRationalGautschi.lean) proves both strict Gautschi bounds $x^{1-u}<\Gamma(x+1)/\Gamma(x+u)<(x+1)^{1-u}$ for all encoded positive rational $x$ and rational $0<u<1$. It verifies that multiplying the original quotient by the original denominator recovers the numerator. [GaussianGammaRationalWendelGautschi](Lean/IPRADerivations/Analysis/GaussianGammaRationalWendelGautschi.lean) proves both strict Wendel bounds on the normalized Gamma quotient and [GaussianGammaRationalWendelBinding](Lean/IPRADerivations/Analysis/GaussianGammaRationalWendelBinding.lean) verifies the defining product with its original denominator. [GaussianGammaRationalWendelBoundary](Lean/IPRADerivations/Analysis/GaussianGammaRationalWendelBoundary.lean) establishes both exact boundary values and the full weak Wendel interval. [GaussianGammaRationalWendelUniformLog](Lean/IPRADerivations/Analysis/GaussianGammaRationalWendelUniformLog.lean) proves the uniform signed logarithmic rate for the original normalized Wendel ratio, including the one-quarter bound on its error coefficient. [GaussianGammaRationalWendelUniform](Lean/IPRADerivations/Analysis/GaussianGammaRationalWendelUniform.lean) proves the uniform relative error $0\le1-Q\le u(1-u)/x\le1/(4x)$ on the original named Wendel quotient for all rational weights in the unit interval. [GaussianGammaDigammaTwoShiftBinding](Lean/IPRADerivations/Analysis/GaussianGammaDigammaTwoShiftBinding.lean) identifies the original normalized two-shift Gamma quotient by its exact product with its denominator. [GaussianGammaDigammaTwoShiftRate](Lean/IPRADerivations/Analysis/GaussianGammaDigammaTwoShiftRate.lean) and [GaussianGammaDigammaTwoShiftRelativeRate](Lean/IPRADerivations/Analysis/GaussianGammaDigammaTwoShiftRelativeRate.lean) prove the C46 logarithmic and relative rates for common-denominator positive rational base and endpoints, with signed rational shifts and the source inequalities on the positive integer shift bound and base. The logarithmic bound is on the certified exponent of the quotient. The exact constants at arbitrary noninteger shift bounds remain open. [GaussianGammaDigammaLipschitz](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLipschitz.lean) proves the original digamma upper slope $2(y-x)$ for common-denominator rational $1\le x\le y$ at independent observation clocks. [GaussianGammaDigammaRescaling](Lean/IPRADerivations/Analysis/GaussianGammaDigammaRescaling.lean) verifies that positive rescaling preserves the native digamma value. [GaussianGammaDigammaDyadicCrossing](Lean/IPRADerivations/Analysis/GaussianGammaDigammaDyadicCrossing.lean) gives the bounded scan for adjacent opposite sample signs under the two endpoint tests. [GaussianGammaDigammaSlopeLowerRational](Lean/IPRADerivations/Analysis/GaussianGammaDigammaSlopeLowerRational.lean) proves the lower slope $(y-x)/4$ on $[1,2]$ with separate rational encodings. [GaussianGammaDigammaDyadicMesh](Lean/IPRADerivations/Analysis/GaussianGammaDigammaDyadicMesh.lean) bounds the increase on adjacent dyadic samples by $4\cdot 2^{-(p+6)}$, and [GaussianGammaDigammaGridSign](Lean/IPRADerivations/Analysis/GaussianGammaDigammaGridSign.lean) passes this bound to the absolute residual when the samples have opposite signs. [GaussianGammaDigammaCriticalSigns](Lean/IPRADerivations/Analysis/GaussianGammaDigammaCriticalSigns.lean) proves $\psi(1)<-1/4$ and $\psi(2)>1/4$ for the original names. [GaussianGammaDigammaDyadicEndpoints](Lean/IPRADerivations/Analysis/GaussianGammaDigammaDyadicEndpoints.lean) verifies their finite grid samples at every prescribed clock, and [GaussianGammaDigammaDyadicLocation](Lean/IPRADerivations/Analysis/GaussianGammaDigammaDyadicLocation.lean) constructs a regular primitive recursive location by comparing selected opposite-sign cells at independent clocks. The checked bound on the sampled digamma residual is $4\cdot 2^{-(p+6)}$. [GaussianGammaDigammaLocationInput](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationInput.lean) identifies the actual frozen inputs of the named integrals with the selected fractions. [GaussianGammaDigammaLocationResidual](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationResidual.lean) lifts the scalar digamma residual to an independent-clock Gaussian distance. [GaussianGammaDigammaLocationProduct](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationProduct.lean) uses a uniform bound on the original Gamma name to give a vanishing residual for the first logarithmic integral. [GaussianGammaDigammaPositiveStationary](Lean/IPRADerivations/Analysis/GaussianGammaDigammaPositiveStationary.lean) proves equality of the original first named logarithmic integral to zero at the completed location and transfers the original first derivative error bound to difference quotients at that point. [GaussianGammaDigammaLocationInterior](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationInterior.lean) places the completed location in $[17/16,31/16]$. [GaussianGammaDigammaLocationValue](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationValue.lean) proves that the actual named quotient $\Gamma^{\prime}/\Gamma$ is zero at this regular interior point. [GaussianGammaPositiveRationalProperness](Lean/IPRADerivations/Analysis/GaussianGammaPositiveRationalProperness.lean) transports original Gamma between encodings with different denominators, radii and lower certificates. [GaussianGammaMinimumSignedStep](Lean/IPRADerivations/Analysis/GaussianGammaMinimumSignedStep.lean) identifies the literal signed small-step endpoint with the weighted chord center and verifies the original derivative rate there. [GaussianGammaMinimumQuotientReadback](Lean/IPRADerivations/Analysis/GaussianGammaMinimumQuotientReadback.lean) recovers the original endpoint variation with the exact step factor. [GaussianGammaMinimumChord](Lean/IPRADerivations/Analysis/GaussianGammaMinimumChord.lean) proves the asymmetric strong chord in both endpoint orders with a squared rational margin uniform in the weight. [GaussianGammaMinimumCenterRate](Lean/IPRADerivations/Analysis/GaussianGammaMinimumCenterRate.lean) transfers the derivative residual to the original log-Gamma endpoint variation along the thin chord. [GaussianGammaMinimumChordStationary](Lean/IPRADerivations/Analysis/GaussianGammaMinimumChordStationary.lean) cancels the weight with the thin-step rate and eliminates the intermediate observation allowances while preserving the strong margin. [GaussianGammaMinimumFreezeRational](Lean/IPRADerivations/Analysis/GaussianGammaMinimumFreezeRational.lean) and [GaussianGammaMinimumFreezeLocation](Lean/IPRADerivations/Analysis/GaussianGammaMinimumFreezeLocation.lean) read the actual named log-Gamma and native positive rational freezes with the independent-clock rate. [GaussianGammaMinimumFreezeOrder](Lean/IPRADerivations/Analysis/GaussianGammaMinimumFreezeOrder.lean) transfers their weak and strict logarithm orders to the original Gamma names. [GaussianGammaNegativeCriticalCorrection](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalCorrection.lean) computes the literal reciprocal correction for every negative interval. [GaussianGammaNegativeCriticalSigns](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalSigns.lean) proves margins of $-5$ and $5$ at the two prescribed endpoints and the corresponding opposite finite signs for the shifted digamma name. [GaussianGammaNegativeCriticalLowerSlope](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalLowerSlope.lean) proves a quarter lower slope throughout the interval, and [GaussianGammaNegativeCriticalSlope](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalSlope.lean) gives the explicit upper slope $2+(N+2)K^2$ on windows where both distances from the poles are at least $1/K$. [GaussianGammaNegativeCriticalGrid](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalGrid.lean) selects adjacent opposite signs at every dyadic mesh with a vanishing sampled residual. [GaussianGammaNegativeCriticalLocation](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalLocation.lean) proves regularity of the original dyadic location, and [GaussianGammaNegativeCriticalLocationInterior](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalLocationInterior.lean) puts it strictly between $-N-1$ and $-N$. [GaussianGammaNegativeCriticalLocationZero](Lean/IPRADerivations/Analysis/GaussianGammaNegativeCriticalLocationZero.lean) constructs the zero value of the shifted digamma at that location by explicit cofinal evaluation. [GaussianGammaNegativeIntervalNative](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNative.lean) proves that the original Gamma name times the literal repeated shift product gives the positive terminal Gamma name at $1+a/b$. [GaussianGammaNegativeIntervalDerivativeTarget](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalDerivativeTarget.lean) verifies the algebraic identities for the proposed derivative target. [GaussianGammaNegativeProductDerivativeCorrection](Lean/IPRADerivations/Analysis/GaussianGammaNegativeProductDerivativeCorrection.lean) identifies the first coefficient of the literal product with the negative of the digamma correction times that product. [GaussianGammaNegativeProductDerivativeRate](Lean/IPRADerivations/Analysis/GaussianGammaNegativeProductDerivativeRate.lean) proves its finite derivative error proportional to the displacement. [GaussianGammaNegativeIntervalProductSign](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalProductSign.lean) bounds the signed product below by $a(b-a)/b^2$ throughout the open interval. [GaussianGammaNegativeIntervalGammaSign](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalGammaSign.lean) gives an explicit positive lower bound on the sign-adjusted original Gamma over encoded rational inputs. [GaussianGammaNegativeIntervalInverseRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalInverseRecurrence.lean) proves the inverse recurrence and identifies its two-term derivative target. [GaussianGammaNegativeIntervalInverseBound](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalInverseBound.lean) and [GaussianGammaNegativeIntervalStep](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalStep.lean) certify bounds and the original positive Euler rate at a native unit step. [GaussianGammaNegativeIntervalDigammaRate](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalDigammaRate.lean) proves that the original negative Gamma difference quotient at any rational input converges along steps $1/D$ to the Gamma value times the literal shifted digamma, and that its normalization by the original Gamma converges to the shifted digamma itself. It supplies an explicit cutoff and separate allowances for both observation clocks. [GaussianGammaNegativeIntervalCriticalQuotientZero](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalCriticalQuotientZero.lean) and [GaussianGammaNegativeIntervalCriticalDerivativeZero](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalCriticalDerivativeZero.lean) prove that actual normalized and unnormalized Gamma quotients at the selected dyadic inputs give regular zero names, with explicit cofinal unit steps. [GaussianGammaNegativeIntervalLogAbsolute](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogAbsolute.lean) verifies that the named exponential of the real logarithm is the original Gamma after correcting its interval sign, and [GaussianGammaNegativeIntervalLogAbsoluteOrder](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogAbsoluteOrder.lean) transfers both weak and strict orders to that magnitude. [GaussianGammaNegativeIntervalLogStrongConvexity](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogStrongConvexity.lean) gives its strong weighted logarithmic comparison with an explicit quadratic margin on every negative rational interval. [GaussianGammaNegativeIntervalChordRate](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalChordRate.lean) gives the original signed thin-chord Gamma derivative rate in either endpoint order. [GaussianGammaNegativeIntervalLogThinChord](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogThinChord.lean) retains $|c-a|^2/(16b^2)$ in the unnormalized chord and [GaussianGammaNegativeIntervalLogChordStationary](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogChordStationary.lean) makes the stationary comparison conditional on the corresponding thin-step logarithmic rate. [GaussianGammaNegativeIntervalUniformLower](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalUniformLower.lean) gives the signed Gamma magnitude a floor independent of its rational encoding, and [GaussianGammaNegativeIntervalLogAbsoluteRetiming](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalLogAbsoluteRetiming.lean) binds the resulting retimed positive logarithm to the original log magnitude. [GaussianGammaNegativeIntervalCriticalComparison](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalCriticalComparison.lean) then proves the strong comparison at the actual selected critical approximants against distinct rational inputs with the same denominator and a common pole margin. Its leading error tends to zero with an interval-dependent coefficient, and the two observation allowances remain independent. [GaussianGammaNegativeIntervalCriticalRationalComparison](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalCriticalRationalComparison.lean) removes the common-denominator and apartness premises while preserving the exact squared gap and the same error. [GaussianGammaNegativeIntervalNamedInput](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedInput.lean) verifies the selected offset's named pole margin, and [GaussianGammaNegativeIntervalNamedInputRetiming](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedInputRetiming.lean) obtains an exact sample collar by reading a sufficiently late observation of any regular real offset with named order margins. [GaussianGammaNegativeIntervalRationalProperness](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalRationalProperness.lean) identifies the decoded critical fraction with the literal grid fraction and proves equal-encoding coherence of the original signed Gamma and log magnitude. [GaussianGammaNegativeIntervalNamedApartness](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedApartness.lean) keeps the squared comparison gap positive at every sufficiently late observation when the offsets are apart. [GaussianGammaNegativeIntervalNamedComparisonTransfer](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedComparisonTransfer.lean) transfers finite comparisons with a persistent margin to the regular names. [GaussianGammaNegativeIntervalNamedDigammaRationalRate](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigammaRationalRate.lean) and [GaussianGammaNegativeIntervalNamedDigamma](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigamma.lean) construct the regular named shifted digamma and bound its distance from the actual rational digamma at every frozen observation. [GaussianGammaNegativeIntervalNamedDigammaInverseSlope](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigammaInverseSlope.lean) carries the lower slope to the named offsets. [GaussianGammaNegativeIntervalNamedDigammaUniqueness](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigammaUniqueness.lean) proves injectivity under separate pole margins. [GaussianGammaNegativeIntervalNamedDigammaRoot](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigammaRoot.lean) identifies the literal critical grid offset as the unique zero, including inputs admitted through named interval order and retiming. [GaussianGammaNegativeIntervalNamedLogTerminal](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedLogTerminal.lean) supplies a modulus for the original positive terminal Gamma across distinct rational encodings, and [GaussianGammaNegativeIntervalNamedLogVariation](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedLogVariation.lean) extends it through the negative shift and logarithm. [GaussianGammaNegativeIntervalNamedLog](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedLog.lean) constructs regular real log-magnitude names by sampling the original evaluations. [GaussianGammaNegativeIntervalNamedLogFrozen](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedLogFrozen.lean) proves the uniform late-freeze bound with independent output clocks. [GaussianGammaNegativeIntervalNamedMinimum](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedMinimum.lean) and [GaussianGammaNegativeIntervalNamedStrictMinimum](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedStrictMinimum.lean) establish the weak log-magnitude minimum and its strict form with positive separation. [GaussianGammaNegativeIntervalNamedGamma](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGamma.lean) identifies Gamma on the named interval by a uniform rate to the literal unscaled rational Gamma evaluator. [GaussianGammaNegativeIntervalNamedExtremum](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedExtremum.lean) proves the parity-dependent Gamma extrema under named interval bounds and preserves strictness when the original offset is apart. [GaussianGammaNegativeIntervalNamedGammaSign](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGammaSign.lean) certifies real observations and the strict interval sign. [GaussianGammaNegativeIntervalNamedDigammaQuotient](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDigammaQuotient.lean) and [GaussianGammaNegativeIntervalNamedSignedDigammaQuotient](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedSignedDigammaQuotient.lean) identify the normalized original forward unit quotients with the named digamma along the explicit cofinal rational freezes. [GaussianGammaNegativeIntervalSignedDigammaQuotient](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalSignedDigammaQuotient.lean) proves exact cancellation of the signed factors. [GaussianGammaNegativeIntervalNamedDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDerivative.lean) gives a uniform rational offset clock and an explicit step cutoff for the original unscaled forward quotients, with limit the product of named Gamma and named digamma. [GaussianNamedApartnessTightness](Lean/IPRADerivations/Analysis/GaussianNamedApartnessTightness.lean) and [GaussianGammaNegativeIntervalNamedExtremumUniqueness](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedExtremumUniqueness.lean) prove that an offset attaining the extremal value equals the selected offset, using finite rational comparisons inside iPRA. [GaussianGammaMinimumRational](Lean/IPRADerivations/Analysis/GaussianGammaMinimumRational.lean) preserves the squared rational separation term with an explicit stationary residual allowance. [GaussianGammaMinimumGlobal](Lean/IPRADerivations/Analysis/GaussianGammaMinimumGlobal.lean) proves that the selected positive location is a global minimum of the original named Gamma on all positive real inputs with a lower certificate, with strict inequality for every input finitely apart from the minimizer. [GaussianGammaNamedPoleFreeModulus](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeModulus.lean), [GaussianGammaNamedPoleFree](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFree.lean), [GaussianGammaNamedPoleFreeEncoding](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeEncoding.lean), and [GaussianGammaNamedPoleFreeFrozen](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeFrozen.lean) construct the regular pole-free complex Gamma evaluator from the original native observations with a uniform disk and pole separation. [GaussianGammaNegativeIntervalNamedGammaNativeDomain](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGammaNativeDomain.lean) certifies the affine negative-interval input, and [GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding.lean) proves equality of the two Gamma names at that input. [GaussianGammaNegativeIntervalNamedTerminalDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedTerminalDerivative.lean) proves the rate for the original positive terminal quotient and preserves the named increment. [GaussianGammaNegativeIntervalInverseRationalEnvelope](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalInverseRationalEnvelope.lean) gives the exact rational inverse-shift difference and quadratic remainder. [GaussianGammaNegativeIntervalNamedInverseFactor](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedInverseFactor.lean) and [GaussianGammaNegativeIntervalNamedCorrectionFactor](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedCorrectionFactor.lean) extend the exact inverse shift and its derivative coefficient to named inputs. [GaussianGammaNegativeIntervalNamedInverseDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedInverseDerivative.lean) proves the named-increment rate for the original inverse factor. [GaussianNamedIncrementProductRule](Lean/IPRADerivations/Analysis/GaussianNamedIncrementProductRule.lean) proves the exact named-increment product rule, and [GaussianGammaNegativeIntervalNamedInverseRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedInverseRecurrence.lean) and [GaussianGammaNegativeIntervalNamedDerivativeRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDerivativeRecurrence.lean) identify the original recurrence and derivative target using common terminal freezes. [GaussianGammaNamedPoleFreeProperness](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeProperness.lean) proves extensionality of the native pole-free evaluator under independent certificates, and [GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient.lean) preserves the original named reciprocal through the affine shift. [GaussianGammaNegativeIntervalNamedIncrementDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedIncrementDerivative.lean) verifies that the original quotient converges to named Gamma times shifted digamma for every regular named real increment satisfying the explicit smallness and separation certificates. [GaussianGammaNegativeIntervalNamedGammaInverse](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedGammaInverse.lean) and [GaussianGammaNegativeIntervalNamedStationary](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedStationary.lean) cancel the nonzero named Gamma factor. [GaussianGammaNegativeIntervalNamedDerivativeMargin](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedDerivativeMargin.lean) proves derivative extensionality across independently certified pole margins. [GaussianGammaNegativeIntervalNamedCritical](Lean/IPRADerivations/Analysis/GaussianGammaNegativeIntervalNamedCritical.lean) gives the actual quotient rate to zero at the selected point and both directions of the critical-point classification for offsets supplied with named interval bounds. [GaussianBohrMollerupUniqueness](Lean/IPRADerivations/Analysis/GaussianBohrMollerupUniqueness.lean) proves effective uniqueness for fixed logarithmic presentations satisfying the internal laws, with a two-chord comparison and cutoff $j=1+a(a+b)2^p$ at $a/b$. [GaussianBohrMollerupPositivePresentation](Lean/IPRADerivations/Analysis/GaussianBohrMollerupPositivePresentation.lean) identifies positive presentations with the actual Gamma name. This gives the fixed-presentation uniqueness claim via these chords. The paper’s specific finite $L_n/U_n$ approximation intervals are separate. |
| 49–53 | Leading Stirling/relative errors, Robbins bounds, every fixed order of log-Stirling and digamma expansions with the signed positive-real-axis remainder, and the actual multiplicative-coefficient/error algorithm. Generic Euler–Maclaurin components need application-specific endpoint and positivity proofs. [GaussianStirlingNames](Lean/IPRADerivations/Analysis/GaussianStirlingNames.lean) constructs the regular real name of $A(x)$ on every encoded positive rational, using the original Gamma and harmonic logarithms. [GaussianStirlingConstant](Lean/IPRADerivations/Analysis/GaussianStirlingConstant.lean) constructs the regular real name of $C=\tfrac12\log(2\pi)$. [GaussianStirlingRecurrence](Lean/IPRADerivations/Analysis/GaussianStirlingRecurrence.lean) gives the original named equality $A(x)-A(x+1)=d(x)$. [StirlingRationalSeries](Lean/IPRADerivations/Analysis/StirlingRationalSeries.lean), [GaussianStirlingRationalTelescopers](Lean/IPRADerivations/Analysis/GaussianStirlingRationalTelescopers.lean), and [GaussianStirlingFiniteSeries](Lean/IPRADerivations/Analysis/GaussianStirlingFiniteSeries.lean) prove the rational finite series estimate, its exact Horner representation, and the matching telescopers with positive margins. [GaussianStirlingDifferenceBrackets](Lean/IPRADerivations/Analysis/GaussianStirlingDifferenceBrackets.lean) proves the original finite odd-series logarithm brackets on the full positive rational domain. [GaussianStirlingDifferenceBounds](Lean/IPRADerivations/Analysis/GaussianStirlingDifferenceBounds.lean) proves the sharp local inequalities and exact rational finite endpoint order. [GaussianStirlingOriginalIntegerLimit](Lean/IPRADerivations/Analysis/GaussianStirlingOriginalIntegerLimit.lean) constructs the regular integer limit name with exact tail $1/(12n)$ and independent observation errors. [GaussianStirlingLogDuplication](Lean/IPRADerivations/Analysis/GaussianStirlingLogDuplication.lean) proves original log-Gamma duplication on the Stirling inputs. [GaussianStirlingDuplication](Lean/IPRADerivations/Analysis/GaussianStirlingDuplication.lean) proves the exact positive rational Stirling duplication identity with the original $C$ and the signed residual $1/2-x\log(1+1/(2x))$. [GaussianStirlingWallisGammaRatio](Lean/IPRADerivations/Analysis/GaussianStirlingWallisGammaRatio.lean) identifies the actual half-integer and integer Gamma ratio with the finite Wallis factor. [GaussianStirlingWallisLogRate](Lean/IPRADerivations/Analysis/GaussianStirlingWallisLogRate.lean) gives its logarithmic rate $12/n+29\cdot 2^{-p}$ for $n\ge 6$ at clock $p$. [GaussianStirlingWallisLogIdentity](Lean/IPRADerivations/Analysis/GaussianStirlingWallisLogIdentity.lean) relates this logarithm exactly to the original Gamma logarithms. [GaussianStirlingDuplicationResidual](Lean/IPRADerivations/Analysis/GaussianStirlingDuplicationResidual.lean) proves the residual bound $1/(4x)+3\cdot 2^{-p}$ on the original name. [GaussianStirlingHalfStep](Lean/IPRADerivations/Analysis/GaussianStirlingHalfStep.lean) derives a distance $64(1/n+2^{-p})$ between original samples at $n+1/2$ and $n$ for $n\ge 6$. [GaussianStirlingConstantIdentification](Lean/IPRADerivations/Analysis/GaussianStirlingConstantIdentification.lean) proves unconditional equality of the actual cofinal integer limit and $C=\tfrac12\log(2\pi)$ in object iPRA. [GaussianStirlingGlobalBounds](Lean/IPRADerivations/Analysis/GaussianStirlingGlobalBounds.lean) retains both sharp finite margins and proves the first-order log remainder bounds under a translated cofinal rate. It derives the rate at integer inputs. [GaussianStirlingRobbins](Lean/IPRADerivations/Analysis/GaussianStirlingRobbins.lean) proves both sharp logarithmic Robbins inequalities, including the explicit lower and upper margins, unconditionally at positive integers. [GaussianStirlingMultiplicative](Lean/IPRADerivations/Analysis/GaussianStirlingMultiplicative.lean) identifies the exponential of the original log remainder with the literal positive rational Stirling quotient and verifies the positive square root and denominator inverse. [GaussianStirlingGlobalBoundsShiftCorrection](Lean/IPRADerivations/Analysis/GaussianStirlingGlobalBoundsShiftCorrection.lean) bounds the elementary part of the cofinal positive-rational shift by $5/n+3\cdot2^{-p}$. [GaussianStirlingGlobalBoundsRemainder](Lean/IPRADerivations/Analysis/GaussianStirlingGlobalBoundsRemainder.lean) proves the exact named finite remainder decomposition. [GaussianStirlingGlobalBoundsTranslatedRate](Lean/IPRADerivations/Analysis/GaussianStirlingGlobalBoundsTranslatedRate.lean) reduces the cofinal rational rate and sharp global bounds to the original fractional log-Gamma increment estimate. [GaussianStirlingMultiplicativeBoundsCaps](Lean/IPRADerivations/Analysis/GaussianStirlingMultiplicativeBoundsCaps.lean) derives the relative error bound $1/(6x)$ for $x\ge1$ from the sharp first-order logarithmic remainder. [GaussianStirlingFactorialRobbins](Lean/IPRADerivations/Analysis/GaussianStirlingFactorialRobbins.lean) proves $1<R_n<12n/(12n-1)$ for the literal factorial ratio and $R_n<1+2^{-p}$ for $n\ge2^p$. [GaussianStirlingGammaFractionalIncrement](Lean/IPRADerivations/Analysis/GaussianStirlingGammaFractionalIncrement.lean) proves the actual fractional log-Gamma estimate and discharges the cofinal hypotheses. It proves the sharp first-order log remainder and the positive finite-series tail for all encoded positive rationals, and both sharp logarithmic Robbins bounds for encoded rationals at least one. [GaussianStirlingFactorialRobbinsExponential](Lean/IPRADerivations/Analysis/GaussianStirlingFactorialRobbinsExponential.lean) proves the classical strict exponential caps for the literal factorial quotient. [GaussianStirlingGlobalMultiplicativeBounds](Lean/IPRADerivations/Analysis/GaussianStirlingGlobalMultiplicativeBounds.lean) proves the strict leading exponential comparison for all encoded positive rationals, the strict relative-error bound for $x\ge1$, and the strict exponential Robbins bounds on $x\ge1$. [GaussianStirlingFactorialRobbinsConventionalRatio](Lean/IPRADerivations/Analysis/GaussianStirlingFactorialRobbinsConventionalRatio.lean) binds that same factorial quotient to the literal conventional formula $R_n n^n\sqrt{2\pi n}=n!e^n$. [GaussianStirlingAllOrderPairedRefinement](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedRefinement.lean) proves a positive reflected inverse-power weight gap uniform under mesh refinement. [GaussianStirlingAllOrderCenteredBernoulli](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderCenteredBernoulli.lean) binds the centered kernel to the original Bernoulli mesh with exact reflection and zero endpoints. [GaussianStirlingExpansionCoefficients](Lean/IPRADerivations/Analysis/GaussianStirlingExpansionCoefficients.lean) proves the fixed-order coefficient recurrence and initial coefficient. [GaussianStirlingExpansionErrorProgram](Lean/IPRADerivations/Analysis/GaussianStirlingExpansionErrorProgram.lean) proves an explicit multiplicative approximation and error algorithm for the original quotient from the corresponding higher logarithmic rate. [GaussianStirlingAllOrderBernoulliShape](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliShape.lean) proves that the actual centered Bernoulli polynomial has a nonnegative coefficient expansion in $4t(1-t)$ with a positive coefficient. [GaussianStirlingAllOrderBernoulliMeshOrder](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliMeshOrder.lean) proves monotonicity on the first half of the literal grid. [GaussianStirlingAllOrderBernoulliMeshRefinement](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliMeshRefinement.lean) proves exact refinement invariance. [GaussianStirlingAllOrderBernoulliMeshMargin](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliMeshMargin.lean) gives the explicit positive gap on the separated subintervals at all refinements. [GaussianStirlingExpansionFirstOrder](Lean/IPRADerivations/Analysis/GaussianStirlingExpansionFirstOrder.lean) identifies the literal first-order output with $1+1/(12x)$ and discharges its analytic premise from the proved rational Robbins bracket. [GaussianStirlingAllOrderBernoulliEnvelope](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliEnvelope.lean) bounds the original centered kernel by its exact midpoint value on the full rational mesh. [GaussianStirlingAllOrderPanelTail](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelTail.lean) proves the uniform reciprocal-power tail for its actual finite weighted panels. [GaussianStirlingAllOrderFirstPanel](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanel.lean) gives the exact partial fraction decomposition of the original first kernel on a panel. [GaussianStirlingCubicRate](Lean/IPRADerivations/Analysis/GaussianStirlingCubicRate.lean) proves the strict signed bracket $1/(12x)-1/(360x^3)<R(x)<1/(12x)$ at every encoded positive rational input, with a cubic rate at independent observations. [GaussianStirlingExpansionSecondOrder](Lean/IPRADerivations/Analysis/GaussianStirlingExpansionSecondOrder.lean) uses that rate to discharge the original multiplicative program through degree two. [GaussianStirlingAllOrderFirstPanelSum](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanelSum.lean) evaluates the original first weighted panel as the literal harmonic interval and reciprocal-square sum. [GaussianStirlingAllOrderFirstPanelSquareError](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanelSquareError.lean) relates the square contribution to one with an explicit finite-mesh rate. [GaussianStirlingAllOrderFirstPanelError](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanelError.lean) gives an explicit two-sided comparison between the literal first panel and twice the original harmonic-log difference. [GaussianStirlingAllOrderBoxProductGap](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBoxProductGap.lean) proves a positive crossed-product gap on separated refinable boxes for the original centered and reflected weight samples. [GaussianStirlingAllOrderFirstPanelImproper](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanelImproper.lean) identifies the original log-Stirling remainder with the actual first centered periodic Bernoulli weighted improper sum and proves its explicit cutoff error $46· 2^{-p}$. [GaussianStirlingAllOrderPanelDerivative](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelDerivative.lean) gives the exact centered derivative complement and endpoint identities. [GaussianStirlingAllOrderDiscreteParts](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderDiscreteParts.lean) verifies exact finite summation by parts, and [GaussianStirlingAllOrderCentralDerivativeBinding](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderCentralDerivativeBinding.lean) identifies the leading quadratic term of the centered finite difference with the actual lower Bernoulli grid, with a two-sided finite error. [GaussianStirlingAllOrderHalfGridMean](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderHalfGridMean.lean) proves the normalized reverse-Chebyshev inequality for the original reflected first-half grids, retaining a positive rational margin independent of refinement. [GaussianStirlingAllOrderPairedReadback](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedReadback.lean) identifies every weighted product with the two original periodic panel rows at its reflected indices. [RationalPowerMoments](Lean/IPRADerivations/Analysis/RationalPowerMoments.lean) verifies the literal scalar monomial average and its $1/M$ mesh error against the exact monomial moment. [GaussianStirlingAllOrderCentralBernoulliError](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderCentralBernoulliError.lean) and [GaussianStirlingAllOrderReciprocalWeightError](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderReciprocalWeightError.lean) verify the quantitative centered second-difference comparisons for the original Bernoulli and reciprocal-power panel factors. [GaussianStirlingAllOrderReciprocalGridError](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderReciprocalGridError.lean) expresses the reciprocal curvature error uniformly on the literal panel grid. [GaussianStirlingAllOrderPairedPanel](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedPanel.lean) reads the original panel as exactly the paired half-grid with the literal midpoint correction. [RationalPolynomialGridSum](Lean/IPRADerivations/Analysis/RationalPolynomialGridSum.lean) verifies a fixed signed polynomial grid fold through the natural power sums. [GaussianStirlingAllOrderPanelPartsRecurrence](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelPartsRecurrence.lean) proves the quantitative integration-by-parts recurrence for the original finite panels with an explicit $1/M$ mesh error, and [GaussianStirlingAllOrderPowerIntegral](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPowerIntegral.lean) gives the adjacent antiderivative brackets for the reciprocal-power mass. The unweighted averages have exact reflected-grid identities with the appropriate midpoint and endpoint corrections in [GaussianStirlingAllOrderPairedWeightFold](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedWeightFold.lean) and [GaussianStirlingAllOrderPairedBernoulliFold](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedBernoulliFold.lean). [GaussianStirlingAllOrderBernoulliGridMean](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliGridMean.lean) identifies the literal centered Bernoulli samples with the signed polynomial whose constant coefficient has been removed. [RationalPolynomialGridMean](Lean/IPRADerivations/Analysis/RationalPolynomialGridMean.lean) proves a two-sided mesh error for every fixed signed polynomial, and [GaussianStirlingAllOrderBernoulliGridRate](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderBernoulliGridRate.lean) specializes the exact moment and error to the original centered Bernoulli mean at each fixed positive order. [GaussianStirlingAllOrderPanelPartsCofinal](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelPartsCofinal.lean) proves an explicit cofinal $2^{-p}$ residual for the exact original weighted and mass prefixes. [GaussianStirlingAllOrderFirstPanelCommonMesh](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFirstPanelCommonMesh.lean) compares the actual first panel on arbitrary fine meshes with its original local logarithmic name. [GaussianStirlingAllOrderPowerIntegralMesh](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPowerIntegralMesh.lean) and [GaussianStirlingAllOrderPowerIntegralCofinal](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPowerIntegralCofinal.lean) identify the original reciprocal-power mass with its exact antiderivative, with a cofinal error uniform over the cutoff. [GaussianStirlingAllOrderPairedWeightMass](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPairedWeightMass.lean) identifies this mass fold with the ordinary weight average used in the reflected comparison. [GaussianStirlingAllOrderPanelPartsBinding](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelPartsBinding.lean) binds the literal cofinal weighted prefixes at every fixed order to the named recurrence based on the original remainder. [GaussianStirlingAllOrderImproperName](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderImproperName.lean) supplies the regular improper name and its equivalence to that recurrence. [GaussianDigammaFirstBernoulliPanelSum](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliPanelSum.lean) splits the first original digamma panel exactly into the literal reciprocal, square and cube mass folds. [GaussianDigammaFirstBernoulliEndpoints](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliEndpoints.lean) identifies the exact square and cube antiderivative correction with the reciprocal endpoint trapezoid. [GaussianStirlingAllOrderFullGridCovariance](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFullGridCovariance.lean) transfers the positive reflected margin to the original full panel with an exact midpoint correction. [GaussianStirlingAllOrderFullGridMeanRate](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderFullGridMeanRate.lean) inserts the signed Bernoulli mean with its mesh allowance, and [GaussianStirlingAllOrderMidpointCorrection](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderMidpointCorrection.lean) bounds the midpoint correction by the current reciprocal-power cap divided by $4S$. [GaussianStirlingAllOrderPanelPositive](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelPositive.lean) and [GaussianStirlingAllOrderPanelPositivePrefix](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderPanelPositivePrefix.lean) prove a uniformly positive lower floor for the first original weighted panel and every nonempty prefix on meshes $8S$. [GaussianDigammaFirstBernoulliHarmonic](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliHarmonic.lean) proves the exact correction between the original left harmonic mass and the verified factorial-harmonic interval. [GaussianStirlingAllOrderLogTruncation](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderLogTruncation.lean) identifies the signed multiple of the actual improper name with the original log-Stirling remainder after subtracting each literal fixed truncation. [GaussianStirlingAllOrderTruncationCoefficients](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderTruncationCoefficients.lean) checks the correction coefficients against the existing log coefficient formula. [GaussianStirlingAllOrderImproperPositive](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderImproperPositive.lean) passes the finite rational floor to the actual improper name and proves strict positivity. [GaussianStirlingAllOrderOuterCovariance](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderOuterCovariance.lean) sums the corrected upper comparison over every nonempty original cutoff while retaining the first-panel margin. [GaussianStirlingAllOrderTruncationHorner](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderTruncationHorner.lean) supplies the exact connection between the literal correction sums and the original Horner program at both parities. [GaussianStirlingAllOrderOuterCovarianceRate](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderOuterCovarianceRate.lean) gives the uniform summed error and [GaussianStirlingAllOrderOuterCovarianceStrict](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderOuterCovarianceStrict.lean) retains a fixed positive rational floor for the strict finite covariance gap. [GaussianStirlingAllOrderSignedLower](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderSignedLower.lean) transports strict positivity to the original oriented truncation error. [GaussianStirlingAllOrderNamedUpperGap](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderNamedUpperGap.lean) transfers the rational floor to the named difference. [GaussianStirlingAllOrderImproperUpper](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderImproperUpper.lean) proves the strict upper comparison on the actual improper name. [GaussianStirlingAllOrderSignedBounds](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderSignedBounds.lean) proves the sharp strict two-sided bound for the oriented original log-Stirling error at every fixed order and every encoded positive rational input. [GaussianDigammaFirstBernoulliLocal](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliLocal.lean) proves the explicit first-panel rate against the real log-difference name. [GaussianDigammaFirstBernoulliReference](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliReference.lean) gives the exact finite reference row as an anchor difference. [GaussianStirlingAllOrderSignedParity](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderSignedParity.lean) gives the original un-oriented parity brackets. [GaussianStirlingAllOrderSharpLogRate](Lean/IPRADerivations/Analysis/GaussianStirlingAllOrderSharpLogRate.lean) transfers those exact bounds to the original Horner errors, discharges the independent-clock log rate for positive rational inputs at least one, and proves the original multiplicative approximation program at every fixed degree under its explicit large-argument guard. [GaussianDigammaFirstBernoulliPrefix](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliPrefix.lean) and [GaussianDigammaFirstBernoulliImproper](Lean/IPRADerivations/Analysis/GaussianDigammaFirstBernoulliImproper.lean) sum the mesh errors and identify the native first cofinal weighted prefix with $\log x-1/(2x)-\psi(x)$, including the explicit required mesh and observation rate. [GaussianDigammaBernoulliRecurrence](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliRecurrence.lean) verifies the recurrence and its mesh rate at every fixed order. [GaussianDigammaBernoulliImproperName](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliImproperName.lean) gives explicit regular names for the literal weighted prefixes and their cross-clock equivalence to the recurrence. [GaussianDigammaBernoulliCoefficients](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliCoefficients.lean) verifies the coefficients against the original Bernoulli table. [GaussianDigammaBernoulliTruncation](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliTruncation.lean) identifies each actual improper name with $(-1)^{m+1}$ times the native error after subtracting the first $m$ inverse even powers on every encoded positive rational. [GaussianDigammaBernoulliActualBase](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliActualBase.lean) and [GaussianDigammaBernoulliActualUpper](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliActualUpper.lean) pass the positive lower floor and the sharp strict upper comparison to the actual improper names. [GaussianDigammaBernoulliRadius](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliRadius.lean) identifies that upper point with the magnitude of the first omitted term. [GaussianDigammaBernoulliSharpRemainder](Lean/IPRADerivations/Analysis/GaussianDigammaBernoulliSharpRemainder.lean) proves the strict signed two-sided bound for the original digamma truncation after every fixed number $m$ of corrections on all encoded positive rationals. |
| 54–58 | [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerCofinal.lean) constructs the canonical Euler logarithm on the signed rational right half-plane from the original heads. Its exponential equals the original Gamma name by [GaussianLogGammaEulerExponentialLimit](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialLimit.lean). The unit shift, normalization at one and positive-rational-axis identity are checked below. The cofinal Taylor comparison with the reciprocal slope is checked below. The actual punctured difference quotient converges to the C27 digamma series on these rational charts. The canonical program also gives a regular log-Gamma evaluator on regular complex names with a certified right-half-plane margin. Its exponential agrees with the original named Gamma, including the overlap with the general pole-free evaluator. The actual named derivative is the cofinal digamma series, with a uniform modulus. The exact unit-shift recurrence holds for regular input names on the same certified right half-plane. On the certified positive real axis the same named evaluator equals the original real log-Gamma. The actual Binet kernel series has the uniform `1/(8N)` truncation bound and the interval estimates recorded below. Its value at zero is `1/12`, which is also the sharp upper bound on the nonnegative axis. [The elementary kernel proof](Lean/IPRADerivations/Analysis/GaussianBinetKernelElementaryRational.lean) identifies its quotient at positive rational times and its value at zero. [The first Binet formula](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormula.lean) identifies the original improper Laplace sampler with the original Stirling remainder on the encoded rational right half-plane. [The named first Binet formula](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormulaNamed.lean) extends the identity to regular complex names with the original positive real-part margin and disk. [The second Binet improper integral](Lean/IPRADerivations/Analysis/GaussianBinetBoseImproperName.lean) is a regular name for the original integrand with checked lower and upper cutoff rates. [The second Binet formula](Lean/IPRADerivations/Analysis/GaussianBinetSecondFormula.lean) identifies twice this original improper integral with the original Stirling remainder on the encoded rational right half-plane. [The named second Binet formula](Lean/IPRADerivations/Analysis/GaussianBinetSecondFormulaNamed.lean) lifts that original sampler to regular complex names with the certified margin and disk. Complete monotonicity, Raabe/unit-interval log-Gamma integrals and the Gamma–zeta Mellin identity for `Re(s)>1` remain open. |
| 59–62 | Wallis product with a rational rate to the original arctangent quadrature checked in [GaussianGammaHalfWallisRate](Lean/IPRADerivations/Analysis/GaussianGammaHalfWallisRate.lean). [GaussianEvenMomentIntegral](Lean/IPRADerivations/Analysis/GaussianEvenMomentIntegral.lean) checks the actual positive-half Gaussian moment relative to the original half-integer Gamma value. [GaussianGammaHalfIntegerValues](Lean/IPRADerivations/Analysis/GaussianGammaHalfIntegerValues.lean) gives its exact factorial coefficient relative to Gamma at one half. [GaussianOddSymmetricQuadrature](Lean/IPRADerivations/Analysis/GaussianOddSymmetricQuadrature.lean) checks exact finite symmetric cancellation for the literal odd Gaussian quadrature. [GaussianGammaHalfPositiveRoot](Lean/IPRADerivations/Analysis/GaussianGammaHalfPositiveRoot.lean) identifies the original value at one half as a positive real square root of the exact arctangent name for pi. [GaussianGammaHalfSqrtPi](Lean/IPRADerivations/Analysis/GaussianGammaHalfSqrtPi.lean) checks its equality with an independent dyadic square-root program. [GaussianGammaHalfWallisConvergence](Lean/IPRADerivations/Analysis/GaussianGammaHalfWallisConvergence.lean) proves the one-sided Wallis rate. [GaussianGammaHalfSqrtValues](Lean/IPRADerivations/Analysis/GaussianGammaHalfSqrtValues.lean) identifies the actual positive half-integer Gamma values and the positive-half even Gaussian moments with the independent square-root sampler and their exact factors. [GaussianEvenMomentSymmetricGrid](Lean/IPRADerivations/Analysis/GaussianEvenMomentSymmetricGrid.lean) checks the original reflected even rows and their finite sums. [GaussianEvenMomentWholeLine](Lean/IPRADerivations/Analysis/GaussianEvenMomentWholeLine.lean) uses the original cofinal endpoints and omitted-tail bounds for both halves. [GaussianEvenMomentWholeLineValue](Lean/IPRADerivations/Analysis/GaussianEvenMomentWholeLineValue.lean) identifies the actual whole-line even moment with the unhalved factorial and independent square-root factors. [GaussianOddMomentWholeAbsolute](Lean/IPRADerivations/Analysis/GaussianOddMomentWholeAbsolute.lean) gives the literal odd absolute convergence to twice the positive-half Euler reference, with exact symmetric cancellation of the signed quadrature. [GaussianOddMomentIndependentCuts](Lean/IPRADerivations/Analysis/GaussianOddMomentIndependentCuts.lean) proves the signed limit is zero at independent left and right cutoffs. Gamma-density normalization and moments are checked. [GaussianEulerIntegerMomentIntegrand](Lean/IPRADerivations/Analysis/GaussianEulerIntegerMomentIntegrand.lean) proves the original weighted Euler row identity at every internal integer order. [GaussianGammaDensityDomain](Lean/IPRADerivations/Analysis/GaussianGammaDensityDomain.lean) derives the shifted integral and Gamma guards. [GaussianEulerIntegerMomentUniform](Lean/IPRADerivations/Analysis/GaussianEulerIntegerMomentUniform.lean) gives a uniform compact clock for the literal weighted rows. [GaussianGammaDensityMomentReference](Lean/IPRADerivations/Analysis/GaussianGammaDensityMomentReference.lean) evaluates the normalized original shifted integral as the rising product. [GaussianEulerIntegerMomentGrid](Lean/IPRADerivations/Analysis/GaussianEulerIntegerMomentGrid.lean) and [GaussianGammaDensityMomentGrid](Lean/IPRADerivations/Analysis/GaussianGammaDensityMomentGrid.lean) bind the literal weighted rows to the normalized cofinal sampler. [GaussianGammaDensityMomentName](Lean/IPRADerivations/Analysis/GaussianGammaDensityMomentName.lean) proves the original density moments for every internal nonnegative integer on the encoded half-plane. [GaussianGammaDensityMeanVariance](Lean/IPRADerivations/Analysis/GaussianGammaDensityMeanVariance.lean) gives normalization, mean and variance for that same sampler. [GaussianNamedGoldenRatio](Lean/IPRADerivations/Analysis/GaussianNamedGoldenRatio.lean) proves the independent positive golden-ratio name satisfies its quadratic identity. [GaussianNamedGoldenRatioFormula](Lean/IPRADerivations/Analysis/GaussianNamedGoldenRatioFormula.lean) binds that sampler to the original affine square-root expression, and [GaussianNamedGoldenRatioUniqueness](Lean/IPRADerivations/Analysis/GaussianNamedGoldenRatioUniqueness.lean) proves uniqueness of its quadratic among certified positive regular names. [GaussianNamedGammaFirstCrossing](Lean/IPRADerivations/Analysis/GaussianNamedGammaFirstCrossing.lean) proves the first Gamma crossing at three halves. [GaussianNamedGammaBackwardIdentification](Lean/IPRADerivations/Analysis/GaussianNamedGammaBackwardIdentification.lean) identifies the original named backward argument with the literal pole-free evaluator at decoded native observations. [GaussianNamedGammaSecondCrossing](Lean/IPRADerivations/Analysis/GaussianNamedGammaSecondCrossing.lean) proves the second crossing exactly at the independent positive golden ratio. [GaussianNamedGammaSecondCrossingWitness](Lean/IPRADerivations/Analysis/GaussianNamedGammaSecondCrossingWitness.lean) proves the literal golden name is admitted and attains the crossing. [GaussianArctangentCayleyValues](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyValues.lean) proves the exact norm and endpoints of the rational Cayley grid. [GaussianArctangentCayleyStep](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyStep.lean) bounds its linear exponential step defect by `2/M²`. [GaussianArctangentExponentialPrefix](Lean/IPRADerivations/Analysis/GaussianArctangentExponentialPrefix.lean) matches the exact arctangent prefix to the original π program. [GaussianArctangentCayleyExponentialStep](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyExponentialStep.lean) and [GaussianArctangentCayleyBudget](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyBudget.lean) give the local exponential defect and mesh budget. [GaussianArctangentQuarterExponential](Lean/IPRADerivations/Analysis/GaussianArctangentQuarterExponential.lean) and [GaussianArctangentExponentialPeriod](Lean/IPRADerivations/Analysis/GaussianArctangentExponentialPeriod.lean) transport the finite endpoint estimate to the original exponential clocks. [GaussianArctangentCayleyTelescope](Lean/IPRADerivations/Analysis/GaussianArctangentCayleyTelescope.lean) proves the finite Cayley estimate at every prefix, and [GaussianArctangentOriginalExponential](Lean/IPRADerivations/Analysis/GaussianArctangentOriginalExponential.lean) proves the exact quarter, half and full turns for the original arctangent name. [GaussianArctangentNamedSine](Lean/IPRADerivations/Analysis/GaussianArctangentNamedSine.lean) proves the period and signed integer zeros of the named sine, and [GaussianArctangentNamedPhase](Lean/IPRADerivations/Analysis/GaussianArctangentNamedPhase.lean) identifies the actual integer and quarter products with the corresponding phase programs. [GaussianNamedGammaFactorialInterpolation](Lean/IPRADerivations/Analysis/GaussianNamedGammaFactorialInterpolation.lean) gives an explicit regular name for the alternative interpolation on the certified right half-plane, its recurrence and factorial values, and its distinction at one quarter for any nonzero rational coefficient. [GaussianGammaPoleFreeSineInterpolation](Lean/IPRADerivations/Analysis/GaussianGammaPoleFreeSineInterpolation.lean) proves the same interpolation program satisfies the recurrence on encoded Gaussian rationals off the original poles, deriving both separation certificates from exact pole exclusion. [GaussianNamedSineTaylor](Lean/IPRADerivations/Analysis/GaussianNamedSineTaylor.lean) identifies the sine factor with its literal signed factorial series at independent precisions. |

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
[GaussianNamedPositiveDigamma](Lean/IPRADerivations/Analysis/GaussianNamedPositiveDigamma.lean), [GaussianGammaPositiveNamedRationalFreeze](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedRationalFreeze.lean), [GaussianGammaDigammaLocationGammaDerivative](Lean/IPRADerivations/Analysis/GaussianGammaDigammaLocationGammaDerivative.lean).

The recurrence gives a strict rational digamma lower slope across arbitrary
positive encodings with a common upper bound. Its inverse bounds the exact
input separation from independent output observations. Freezing the original
named reciprocal and Euler derivative together transports the bound to regular
positive real names. The original derivative vanishes precisely at the
selected location, under arbitrary independently chosen positive margins.
[GaussianGammaDigammaCompactSlopeLower](Lean/IPRADerivations/Analysis/GaussianGammaDigammaCompactSlopeLower.lean), [GaussianRationalLowerSlopeDistance](Lean/IPRADerivations/Analysis/GaussianRationalLowerSlopeDistance.lean), [GaussianGammaDigammaCompactInverseSlope](Lean/IPRADerivations/Analysis/GaussianGammaDigammaCompactInverseSlope.lean), [GaussianGammaPositiveNamedReciprocalFrozen](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedReciprocalFrozen.lean), [GaussianGammaPositiveNamedDigammaFrozen](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedDigammaFrozen.lean), [GaussianGammaPositiveNamedDigammaInjective](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedDigammaInjective.lean), [GaussianNamedPositiveDigammaProperness](Lean/IPRADerivations/Analysis/GaussianNamedPositiveDigammaProperness.lean), [GaussianGammaPositiveNamedCritical](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedCritical.lean).

The original positive digamma is equivalent to a name with exact real
observations. The quantitative rational upper bound controls late finite
observations whose order differs from the named input order by observation
error. This gives exact strict monotonicity on the named positive domain.
[GaussianGammaDigammaCompactLipschitz](Lean/IPRADerivations/Analysis/GaussianGammaDigammaCompactLipschitz.lean), [GaussianNamedPositiveDigammaReal](Lean/IPRADerivations/Analysis/GaussianNamedPositiveDigammaReal.lean), [GaussianGammaPositiveNamedDigammaOrder](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedDigammaOrder.lean).

The two original normalized Euler digamma names at a positive real input
and its unit shift satisfy the digamma recurrence. A common frozen
positive rational observation gives the literal shift with a shared
denominator. The positive margin supplies a reciprocal certificate
for the original input. The comparison rate removes the observation
errors from both digamma terms and the reciprocal.
[GaussianGammaPositiveNamedDigammaRecurrenceInput](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedDigammaRecurrenceInput.lean), [GaussianGammaPositiveNamedDigammaRecurrence](Lean/IPRADerivations/Analysis/GaussianGammaPositiveNamedDigammaRecurrence.lean).

For every internal derivative order `m ≥ 1`, the literal signed
polygamma tail on a certified Gaussian-rational disk satisfies the
C30 bound `(m−1)! · 2^(m+1) / N^m`. The cutoff meets `N ≥ 2R` and
`N ≥ 1` and the finite last index is arbitrary. The proof computes
the reciprocal powers of the actual translated numerator and keeps
their original signed factorial scaling.
[GaussianGammaPolygammaTailRows](Lean/IPRADerivations/Analysis/GaussianGammaPolygammaTailRows.lean), [GaussianGammaPolygammaTail](Lean/IPRADerivations/Analysis/GaussianGammaPolygammaTail.lean).

The C29 regular series evaluator uses the literal signed prefix from
the zeroth term, with a primitive-recursive cofinal cutoff. The pole
certificate excludes zero denominators at every index. Its comparison
with any admissible cutoff retains the C30 bound and the dyadic
observation error. Identifying the series with the corresponding
derivative remains open.
[GaussianGammaPolygammaPrefix](Lean/IPRADerivations/Analysis/GaussianGammaPolygammaPrefix.lean), [GaussianGammaPolygammaSeriesName](Lean/IPRADerivations/Analysis/GaussianGammaPolygammaSeriesName.lean).

## Real Gamma away from the poles

A single late sample of a real pole-free input gives a positive margin or
a computed negative interval chart. In the negative case the two adjacent
pole separations certify a regular offset, and the literal affine shift
recovers the original input. The positive and negative quotient transfers
both preserve the caller's original reciprocal of the increment. One
computed demand supplies both derivative guards and preserves the pole
separation of the perturbed input.
[GaussianGammaNamedHalfPlanePoleFree](Lean/IPRADerivations/Analysis/GaussianGammaNamedHalfPlanePoleFree.lean), [GaussianGammaNamedHalfPlanePoleFreeQuotient](Lean/IPRADerivations/Analysis/GaussianGammaNamedHalfPlanePoleFreeQuotient.lean), [GaussianGammaNamedPoleFreePositiveAdmission](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreePositiveAdmission.lean), [GaussianGammaNamedPoleFreeNegativeSnapshot](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeNegativeSnapshot.lean), [GaussianGammaNamedPoleFreeRealAdmission](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeRealAdmission.lean), [GaussianGammaNamedPoleFreeNegativeChartDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeNegativeChartDerivative.lean), [GaussianGammaNamedPoleFreeIncrementSource](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeIncrementSource.lean), [GaussianGammaNamedRealDerivativeDemand](Lean/IPRADerivations/Analysis/GaussianGammaNamedRealDerivativeDemand.lean).

The sign of the same late observation selects the derivative program,
using a fixed branch for every subsequent observation. For an arbitrary
regular real increment with a reciprocal certificate and the computed
smallness bound, the actual pole-free quotient has an independent-clock
rate to this derivative. A nonzero dyadic increment meets the demand
at each precision. The derivative is zero exactly at the selected
positive location or the selected offset in the computed negative chart.
[GaussianNameBranch](Lean/IPRADerivations/Analysis/GaussianNameBranch.lean), [GaussianGammaNamedRealDerivativeStep](Lean/IPRADerivations/Analysis/GaussianGammaNamedRealDerivativeStep.lean), [GaussianGammaNamedRealDerivative](Lean/IPRADerivations/Analysis/GaussianGammaNamedRealDerivative.lean), [GaussianGammaNamedRealCritical](Lean/IPRADerivations/Analysis/GaussianGammaNamedRealCritical.lean).

A shared explicit dyadic increment meets the demands at two equivalent
inputs. Their original pole-free quotients agree under independent radius
and pole-separation certificates. Combining the two rates gives exact
extensionality of the derivative. On the positive domain, equality with
the selected minimum value excludes every finite apartness witness,
so the input name is equivalent to the selected minimizer.
[GaussianNamedDyadicIncrement](Lean/IPRADerivations/Analysis/GaussianNamedDyadicIncrement.lean), [GaussianGammaNamedPoleFreeQuotientProperness](Lean/IPRADerivations/Analysis/GaussianGammaNamedPoleFreeQuotientProperness.lean), [GaussianGammaNamedRealDerivativeProperness](Lean/IPRADerivations/Analysis/GaussianGammaNamedRealDerivativeProperness.lean), [GaussianGammaMinimumGlobalUniqueness](Lean/IPRADerivations/Analysis/GaussianGammaMinimumGlobalUniqueness.lean).

## The right-half-plane logarithm and finite Euler heads

For a rational input with positive real numerator and positive common
denominator, the actual radial program reads half the logarithm of the
squared modulus. Its exponential agrees with an independent dyadic
square-root program. The signed phase uses the arctangent on the unit
interval and the reciprocal chart beyond it. Equal ratios give exactly
equivalent phase names. The combined logarithm has the positive-axis
readback and positive rational scaling formula of the source.
[GaussianNamedHalf](Lean/IPRADerivations/Analysis/GaussianNamedHalf.lean), [GaussianPositiveRationalHalfLogarithm](Lean/IPRADerivations/Analysis/GaussianPositiveRationalHalfLogarithm.lean), [GaussianRightHalfPlaneRadialLogarithm](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneRadialLogarithm.lean), [GaussianRightHalfPlaneArgument](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgument.lean), [GaussianRightHalfPlaneArgumentProperness](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentProperness.lean), [GaussianRightHalfPlaneArgumentAxis](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentAxis.lean), [GaussianRightHalfPlaneLogarithm](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithm.lean).

The small-chart phase exponential has the exact Cayley square and
nonnegative real part at every observation. Both reciprocal and
conjugate charts have explicit exponential transfer.
[GaussianRightHalfPlaneArgumentExponential](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentExponential.lean), [GaussianRightHalfPlaneArgumentCosine](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentCosine.lean), [GaussianRightHalfPlaneArgumentExponentialBranches](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentExponentialBranches.lean).

In the direct phase chart, the positive radial representative times
the original phase exponential recovers the exact encoded fraction.
Their product squared is the square of the input. The finite real
margin of the sum licenses original reciprocal cancellation,
which selects the desired square root.
[GaussianNamedSquareBranch](Lean/IPRADerivations/Analysis/GaussianNamedSquareBranch.lean), [GaussianRightHalfPlaneExponentialMargin](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneExponentialMargin.lean), [GaussianRightHalfPlaneExponentialSmall](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneExponentialSmall.lean).

The reciprocal phase chart follows by interchanging the numerator
magnitudes and applying the exact quarter turn to the conjugate
exponential. Conjugation then implements the negative imaginary
sign. The exponential of the full logarithm recovers the same
signed fraction program used in the original finite Euler heads
at every admitted encoded Gaussian rational.
[GaussianRightHalfPlaneExponentialCharts](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneExponentialCharts.lean), [GaussianRightHalfPlaneLogarithmExponential](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmExponential.lean).

A common precision computed from the number of terms gives a regular
sum of the actual shifted logarithms. This yields the finite Euler head
`log(N!) + z log(N) − Σ Log(z+k)` on the rational right half-plane.
The cofinal limit and its exponential identity with the original
Gamma evaluator are constructed below.
[GaussianNamedFiniteSumFamily](Lean/IPRADerivations/Analysis/GaussianNamedFiniteSumFamily.lean), [GaussianLogGammaEulerHead](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerHead.lean).

Common positive rescaling of both numerators and the denominator
preserves the complete logarithm name. For any internal positive
integer `k`, the same program satisfies
`Log(z+k) = log(k) + Log(1+z/k)` with the original sign bit and
the exact shifted numerator and residual denominator.
[GaussianRightHalfPlaneLogarithmRescale](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmRescale.lean).

Finite sums of regular names now have checked first-row and final-row
splits, transport under bounded row equivalence, and additivity.
These statements compare the actual count-dependent samplers at
independent observation clocks.
[GaussianNamedFiniteSumFamilySplit](Lean/IPRADerivations/Analysis/GaussianNamedFiniteSumFamilySplit.lean), [GaussianNamedFiniteSumFamilyCongruence](Lean/IPRADerivations/Analysis/GaussianNamedFiniteSumFamilyCongruence.lean), [GaussianNamedFiniteSumFamilyAdd](Lean/IPRADerivations/Analysis/GaussianNamedFiniteSumFamilyAdd.lean).

For every positive internal cutoff `N`, the same finite Euler head has
the value `z log(N) − (Log(z) + Σ_{k=1}^N Log(1+z/k))` at
independent observation clocks. An internal finite sum of the integer
logarithms equals `log(N!)`, which cancels after splitting each
denominator row. The bounded prefix and interval split reads the exact
original row at its offset.
[GaussianLogGammaFactorialLogSum](Lean/IPRADerivations/Analysis/GaussianLogGammaFactorialLogSum.lean), [GaussianLogGammaEulerFactorSum](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerFactorSum.lean), [GaussianLogGammaEulerNormalizedHead](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNormalizedHead.lean), [GaussianNamedFiniteSumFamilyRange](Lean/IPRADerivations/Analysis/GaussianNamedFiniteSumFamilyRange.lean).

On the signed rational disk `|w| ≤ 1/8`, the actual canonical logarithm
of `1+w` equals the actual Mercator logarithm at independently chosen
precisions. Both logarithms exponentiate to the same encoded rational.
The late difference samples have norm at most `3/4`, where the
quadratic exponential remainder gives an internal uniqueness proof.
[GaussianFiniteExponentialLocalUniqueness](Lean/IPRADerivations/Analysis/GaussianFiniteExponentialLocalUniqueness.lean), [GaussianNamedExponentialLocalUniqueness](Lean/IPRADerivations/Analysis/GaussianNamedExponentialLocalUniqueness.lean), [GaussianRightHalfPlaneLogarithmMercator](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmMercator.lean).

The exact difference between two finite Euler heads is the weighted
positive-real logarithm difference minus the sum of the canonical
residual logarithms on the intervening interval. Given a bound `R`
for `|z|`, a row at `k ≥ 8R` differs from its linear term `z/k`
by at most `R²/k²` plus its explicit observation error. The linear
terms sum exactly to `z(H_{N+r}−H_N)`, which also approximates
`z(log(N+r)−log(N))` with error `R/N` plus its observation error.
[GaussianLogGammaEulerNormalizedDifference](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNormalizedDifference.lean), [GaussianLogGammaEulerResidualCanonicalError](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerResidualCanonicalError.lean), [GaussianLogGammaEulerLinearInterval](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerLinearInterval.lean), [GaussianLogGammaEulerWeightedIntervalError](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerWeightedIntervalError.lean).

For any independently chosen observation precisions, the original Euler
heads at `N+r` and `N` differ by at most `(R²+R)/N` plus the two
observation errors when `N ≥ max(1,2R)`. The residual sum uses the
original count-dependent sampler, which absorbs its row count into the
observation precision. A primitive-recursive schedule gives a regular
cofinal name, independent of the chosen admissible radius. The concrete
radius `A+B` covers every signed rational admitted by the original
right-half-plane certificate. The half-disk branch proof below gives
the source threshold `N ≥ 2R`.
[GaussianLogGammaEulerResidualInterval](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerResidualInterval.lean), [GaussianLogGammaEulerHeadGap](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerHeadGap.lean), [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerCofinal.lean).

Exponentiating the negative of either finite Euler logarithm head
gives the original reciprocal Euler head at independently chosen
precisions. The proof identifies each shifted signed rational factor,
uses the original integer logarithm in the weighted exponent, and
folds the exponential product at every internal finite length.
[GaussianLogGammaEulerExponentialHead](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialHead.lean), [GaussianLogGammaEulerExponentialFold](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialFold.lean).

The actual exponential of the canonical cofinal log-Gamma equals the
original Gamma sampler at every admitted signed Gaussian rational.
The reciprocal identity uses the original C7 name and the pole margin
`1/D`. The checked cofinal values agree across any two presentations
with equal canonical rational arguments, including distinct sign bits
for a zero imaginary part.
[GaussianLogGammaEulerRepresentation](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerRepresentation.lean), [GaussianLogGammaEulerExponentialLimit](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialLimit.lean).

The original finite head satisfies the exact unit shift with correction
`Log(z)+log(N)−Log(z+N+1)`, after factorial cancellation and
reindexing the denominator sum. With `S` bounding `|z+1|` and
`N ≥ 8S`, the terminal observation differs from the integer logarithm
by at most `2S/N` plus a dyadic observation error. A common computed
cutoff proves `L(z+1)−L(z)=Log(z)` for the canonical cofinal names
at independent precisions.
[GaussianLogGammaEulerRecurrenceFinite](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerRecurrenceFinite.lean), [GaussianLogGammaEulerTerminalShiftError](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTerminalShiftError.lean), [GaussianLogGammaEulerRecurrence](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerRecurrence.lean).

At `z=1`, the original denominator sum equals `log((N+1)!)`.
The finite Euler logarithm is therefore `log(N)−log(N+1)` and
converges to zero. This normalizes the canonical log-Gamma at every
encoding of the rational one. The positive exponential of each finite
head also equals the original finite Gamma inverse on its pole-safe
domain.
[GaussianLogGammaEulerNormalization](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNormalization.lean), [GaussianLogGammaEulerExponentialFiniteGamma](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialFiniteGamma.lean).

The finite Euler expression for the complex slope uses the original
integer logarithm and the literal reciprocal sum through index `N`.
For positive indices, each reciprocal differs from the corresponding
harmonic term by at most `R/k²` on a certified right-half-plane input.
[GaussianLogGammaEulerReciprocalSlope](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerReciprocalSlope.lean).

Summing the reciprocal-row error and comparing it with the actual
integer-logarithm increment gives an Euler slope tail of `(R+1)/N`
at every positive cutoff. A primitive-recursive cofinal slope name
has this convergence rate with independent observation errors on the
signed rational right half-plane. Its Taylor comparison with the canonical logarithm is proved below.
[GaussianLogGammaEulerReciprocalSlopeGap](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerReciprocalSlopeGap.lean), [GaussianLogGammaEulerReciprocalSlopeCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerReciprocalSlopeCofinal.lean).

The difference of the two original finite log-Gamma heads at a common
cutoff is the displacement times the original integer logarithm minus
the sum of the original shifted logarithm increments. Each relative
step has an exact reciprocal expression and a checked quadratic
Mercator observation error. Its exponential, multiplied by the base
argument, recovers the later rational argument. Coordinate and chart
ratio bounds come from the same native displacement.
[GaussianLogGammaEulerArgumentIncrement](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerArgumentIncrement.lean), [GaussianRightHalfPlaneLogarithmRelativeStep](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmRelativeStep.lean), [GaussianRightHalfPlaneLogarithmRelativeExponential](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmRelativeExponential.lean).

The canonical logarithm agrees with the original Mercator logarithm
on the closed signed rational disk `|w| ≤ 1/2`. The proof bounds the
original radial name using the harmonic rectangle sums and selects the
logarithm by the fourth-root separation estimate. The same Euler
residual sampler now has its quadratic bound as soon as `k ≥ 2R`.
[GaussianRightHalfPlaneLogarithmHalfDiskBound](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmHalfDiskBound.lean), [GaussianLogGammaEulerResidualHalfDisk](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerResidualHalfDisk.lean), [GaussianLogGammaEulerCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerCofinal.lean).

The canonical positive-rational observations lie on the real axis.
Their exponential is the original positive Gamma, so real
exponential injectivity identifies them with the existing real
log-Gamma evaluator for either sign encoding of zero imaginary part.
The finite linear rows also sum to the exact displacement times the
original reciprocal sum. The squared row errors have a uniform finite
majorant, with the observation errors counted explicitly.
[GaussianLogGammaEulerPositiveAxis](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerPositiveAxis.lean), [GaussianLogGammaEulerLinearSlope](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerLinearSlope.lean), [GaussianLogGammaEulerTaylorMajorant](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTaylorMajorant.lean).

For two sufficiently close signed rational inputs on the certified
right half-plane, the actual difference of their canonical logarithms
equals the relative Mercator name. The argument charts agree at unit
ratio, and the radial and angular comparisons keep the corrected name
inside the exponential uniqueness radius. At row `k`, the original
logarithm increment differs from its linear reciprocal term by at most
`4H²/(A+kD)²` plus its common-clock dyadic observation allowance.
[GaussianRightHalfPlaneArgumentContinuity](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneArgumentContinuity.lean), [GaussianRightHalfPlaneRadialContinuity](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneRadialContinuity.lean), [GaussianRightHalfPlaneLogarithmIncrement](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmIncrement.lean).

At every positive internal cutoff, the original finite Euler
logarithm increment differs from the actual displacement times the
finite slope by at most `4H²(K²+2)/D²+25/2^p` at common precision
`p`. Here `H` bounds the native displacement, `D` is the common
denominator, and `K` bounds the reciprocal real margin. The observation
allowance is uniform in the cutoff. A computed admission from the two
real margins and the common size bound supplies the local logarithm
guards for sufficiently small displacements.
[GaussianLogGammaEulerTaylorRows](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTaylorRows.lean), [GaussianLogGammaEulerTaylorFinite](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTaylorFinite.lean), [GaussianRightHalfPlaneLogarithmIncrementMargin](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmIncrementMargin.lean).

The same quadratic bound holds for the cofinal logarithm increment
and the displacement times the cofinal reciprocal slope. Both original
observation precisions are independent. The uniform theorem uses a
common real margin, a common size bound and an explicit displacement
threshold. For a nonzero displacement, the native integer square root
provides positive lower and upper norm margins and a checked bound on
the actual reciprocal.
[GaussianLogGammaEulerTaylorCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTaylorCofinal.lean), [GaussianLogGammaEulerTaylorUniform](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerTaylorUniform.lean), [GaussianLogGammaEulerStepReciprocal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerStepReciprocal.lean).

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
[GaussianLogGammaEulerDerivativeQuotient](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDerivativeQuotient.lean), [GaussianLogGammaEulerDigammaFractionsRate](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDigammaFractionsRate.lean), [GaussianLogGammaEulerDigammaFractionsCofinal](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDigammaFractionsCofinal.lean), [GaussianLogGammaEulerDigammaDerivative](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDigammaDerivative.lean).

For a regular complex name with a certified positive real margin
`1/M`, the actual retimed observations admit a signed rational chart
with real part at least `1/(2M)` and a single computed disk bound.
The chart decoding preserves the exact value of each observation,
including comparisons between observations with different denominators.
[GaussianNamedRightHalfPlaneSigned](Lean/IPRADerivations/Analysis/GaussianNamedRightHalfPlaneSigned.lean).

On a common positive real margin `1/K`, the actual finite complex
reciprocal sums have variation bounded by `(K²+2)|z-w|` across rational
representations with independent denominators. The same leading bound
holds for the cofinal Euler slope and the C27 digamma series, with one
dyadic error for each independently chosen output observation. Retiming
the actual input observations gives a regular digamma name on the
certified right half-plane. Equivalent input names on a common margin
and disk give equivalent digamma names.
[GaussianLogGammaEulerSlopeContinuity](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerSlopeContinuity.lean), [GaussianLogGammaEulerDigammaContinuity](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDigammaContinuity.lean), [GaussianLogGammaEulerNamedDigamma](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedDigamma.lean).

The shared evaluator lift allocates half of each observation error to
retiming the input and half to evaluating at the resulting rational
chart. It proves the exact independent rate to the rational evaluator
at any sufficiently late input observation.
[GaussianNamedRightHalfPlaneLift](Lean/IPRADerivations/Analysis/GaussianNamedRightHalfPlaneLift.lean).

Two independently retimed samples of regular names with a common
real margin can be placed over their literal product denominator.
The common charts preserve both values and both disk bounds. The native
displacement radius is bounded by twice the distance bound times this
denominator, including at zero for the continuity radius. For distinct
samples under the explicit local guard, the quotient of their rational
log-Gamma names has leading error `16P(K²+2)/Q` to the original digamma
partial fractions at the base sample, where `P/Q` bounds their distance
and `K=2M` bounds the reciprocal real margin of the samples.
[GaussianLogGammaEulerCommonDenominator](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerCommonDenominator.lean), [GaussianLogGammaEulerSampleDigamma](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerSampleDigamma.lean).

The named digamma program agrees with the C27 series when the input
is an admissible constant name for a signed rational. The same program
has an independent comparison with a series evaluated at any sufficiently
late original input observation, with leading error `2⁻ˢ` for the verified
freeze clock at precision `s`.
[GaussianLogGammaEulerNamedDigammaRational](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedDigammaRational.lean).

The original cofinal slope is uniformly bounded on each certified
rational disk and real margin. This gives a local modulus for the
cofinal log-Gamma program via the checked quadratic estimate. Exact
rescaling of the finite shifted logarithm rows preserves the original
cofinal value, so the proof applies to observations with independent
denominators. The resulting named evaluator is regular, is proper on
each common certified domain and has the independent `2⁻ˢ` freeze rate
to its original rational program.
[GaussianLogGammaEulerReciprocalSlopeBound](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerReciprocalSlopeBound.lean), [GaussianLogGammaEulerRationalContinuity](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerRationalContinuity.lean), [GaussianLogGammaEulerRescale](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerRescale.lean), [GaussianLogGammaEulerNamed](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamed.lean).

Every original right-half-plane rational chart also gives a certified
constant complex name. Its real margin is the reciprocal of the positive
integer denominator, and the theorem supplies the decoded chart certificate
at the common sample margin.
[GaussianNamedRightHalfPlaneConstant](Lean/IPRADerivations/Analysis/GaussianNamedRightHalfPlaneConstant.lean).

The actual exponential of the named log-Gamma program agrees with
the original complex Gamma evaluator on the certified right half-plane.
A common late observation gives the rational exponential identity,
and a radius bound and the original evaluator clocks remove the freeze
error. The same equality holds with the general pole-free Gamma program
on their common certified domain.
[GaussianNamedRadiusExponentialFreeze](Lean/IPRADerivations/Analysis/GaussianNamedRadiusExponentialFreeze.lean), [GaussianLogGammaEulerExponentialFrozen](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerExponentialFrozen.lean), [GaussianLogGammaEulerNamedExponential](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedExponential.lean).

For regular complex inputs on a common certified disk and real margin,
the actual named log-Gamma increment has a quadratic comparison with
the named displacement times the named digamma. If `P/Q` bounds the
input distance and satisfies the explicit local admission inequality,
the leading output error is `16P²(K²+2)/Q²` with `K=2M`. A computed
finite sample removes the auxiliary freeze error, leaving independent
dyadic observation errors. The comparison includes coincident inputs.
[GaussianNamedLogGammaTaylorFrozen](Lean/IPRADerivations/Analysis/GaussianNamedLogGammaTaylorFrozen.lean), [GaussianNamedLogGammaTaylorEstimate](Lean/IPRADerivations/Analysis/GaussianNamedLogGammaTaylorEstimate.lean).

For apart inputs, the actual log-Gamma quotient uses the verified
named reciprocal of their displacement. It converges to the named
digamma with leading error `192P(K²+2)/Q`, independent of the supplied
apartness witness. A bounded search finds the earliest witness, giving
a reciprocal bound comparable to the displacement. Witness equivalence
transfers the result back to the original quotient program. In
particular `192P(K²+2)2ʳ ≤ Q` suffices for leading error `2⁻ʳ`.
[GaussianNamedTaylorDifferenceQuotient](Lean/IPRADerivations/Analysis/GaussianNamedTaylorDifferenceQuotient.lean), [GaussianNamedMinimumApartness](Lean/IPRADerivations/Analysis/GaussianNamedMinimumApartness.lean), [GaussianNamedLogGammaDerivativeUniform](Lean/IPRADerivations/Analysis/GaussianNamedLogGammaDerivativeUniform.lean).

On positive rational inputs, the literal complex digamma series
agrees with the original real `Γ′/Γ` evaluator. The finite formulas
differ by one terminal reciprocal, which is bounded by `1/N`.
For every certified positive real name, a shared late observation
then identifies the two actual named evaluators. The comparison with
the original `Γ′/Γ` programs at nonreal inputs remains open.
[GaussianLogGammaEulerDigammaPositiveAxis](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerDigammaPositiveAxis.lean), [GaussianLogGammaEulerNamedDigammaPositiveAxis](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedDigammaPositiveAxis.lean).

The canonical right-half-plane logarithm is also a regular named
evaluator, with a local rational modulus and a checked late-observation
rate. The named unit shift uses the actual addition clock. Its signed
rational sample is exactly the base sample with its real numerator
increased by its denominator. Exact cofinal chart agreement aligns the
two representations of that shifted sample. Comparing the three named
evaluations at the same base observation proves
`ℒ(z+1) − ℒ(z) = Log z`. The theory can compute both disk bounds directly
from the original and shifted input names.
[GaussianRightHalfPlaneLogarithmNamed](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmNamed.lean), [GaussianLogGammaEulerChartAgreement](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerChartAgreement.lean), [GaussianLogGammaEulerShiftedChart](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerShiftedChart.lean), [GaussianLogGammaEulerNamedRecurrence](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedRecurrence.lean).

The canonical named log-Gamma agrees with the original real log-Gamma
on every certified positive real name. At a sufficiently late real
observation, exact rational chart agreement identifies the two inputs
to the already proved positive-rational identity. This yields equality
of the actual named evaluators for every admissible disk bound.
[GaussianLogGammaEulerNamedPositiveAxis](Lean/IPRADerivations/Analysis/GaussianLogGammaEulerNamedPositiveAxis.lean).

For the complex digamma comparison used in the first Binet formula,
the actual reciprocal at any rational tag in a horizontal unit cell
differs from the left reciprocal by at most the adjacent difference of
positive real reciprocals. The same sharp bound holds for the literal
finite average over the tags. For a small horizontal step the original
canonical logarithm observations satisfy the quadratic estimate with
the actual rational width times the left reciprocal as linear term.
[GaussianBinetReciprocalRows](Lean/IPRADerivations/Analysis/GaussianBinetReciprocalRows.lean), [GaussianBinetReciprocalMean](Lean/IPRADerivations/Analysis/GaussianBinetReciprocalMean.lean), [GaussianBinetLogHorizontalStep](Lean/IPRADerivations/Analysis/GaussianBinetLogHorizontalStep.lean).

At a common horizontal unit mesh, the actual logarithm increment
approaches the literal reciprocal average. At any internal prefix
length `N`, quantifier-free induction compares the logarithm
increment to the original reciprocal sum, with leading bound
`1/Re(z) − 1/(Re(z)+N)`. The finite Euler slope shares the same
reciprocal prefix. Comparing its terminal real logarithm to the
shifted canonical logarithm and passing to the cofinal names proves
`|ψ(z)−Log(z)| ≤ 1/Re(z)` for every signed rational chart in the
right half-plane. The statement allows independent observation clocks.
[GaussianBinetLogCellGrid](Lean/IPRADerivations/Analysis/GaussianBinetLogCellGrid.lean), [GaussianBinetLogCellComparison](Lean/IPRADerivations/Analysis/GaussianBinetLogCellComparison.lean), [GaussianBinetReciprocalPrefix](Lean/IPRADerivations/Analysis/GaussianBinetReciprocalPrefix.lean), [GaussianBinetDigammaLogBound](Lean/IPRADerivations/Analysis/GaussianBinetDigammaLogBound.lean).

The complex Stirling remainder uses the actual cofinal log-Gamma, the
canonical logarithm and the named Stirling constant. Its restriction to
the positive real axis agrees exactly with the original real remainder,
including the sharp absolute bound `1/(12x)`. The canonical recurrence
gives its exact unit difference
`R(z)−R(z+1) = (z+1/2)(Log(z+1)−Log(z))−1`.
[GaussianBinetStirlingRemainder](Lean/IPRADerivations/Analysis/GaussianBinetStirlingRemainder.lean), [GaussianBinetStirlingRealBound](Lean/IPRADerivations/Analysis/GaussianBinetStirlingRealBound.lean), [GaussianBinetStirlingUnitDifferenceAlgebra](Lean/IPRADerivations/Analysis/GaussianBinetStirlingUnitDifferenceAlgebra.lean), [GaussianBinetStirlingUnitDifference](Lean/IPRADerivations/Analysis/GaussianBinetStirlingUnitDifference.lean).

On the original uniform grid of `[0,1]`, the weighted resolvent
`(1/2−t)/(z+t)` has an exact affine reduction at every tag. Its literal
finite sum and cofinal quadrature agree with the canonical logarithm
increment expression. The resulting cofinal unit quadrature equals
the actual remainder difference `R(z)−R(z+1)`.
[GaussianBinetWeightedResolventGrid](Lean/IPRADerivations/Analysis/GaussianBinetWeightedResolventGrid.lean), [GaussianBinetWeightedResolvent](Lean/IPRADerivations/Analysis/GaussianBinetWeightedResolvent.lean).

The actual unit grid for `(1/2−u) exp(−tu)` has a checked mesh and
observation error against the elementary endpoint primitive. At
positive rational `t`, the regular cofinal name equals
`(1+exp(−t))/(2t)−(1−exp(−t))/t²`. At zero the literal left grid of
size `N` gives `1/(2N)` and its cofinal value is zero.
[GaussianBinetWeightedExponentialAlgebra](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialAlgebra.lean), [GaussianBinetWeightedExponentialGrid](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialGrid.lean), [GaussianBinetWeightedExponentialZero](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialZero.lean), [GaussianBinetWeightedExponential](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponential.lean).

On a bounded interval `0 ≤ t ≤ T`, the weighted exponential unit
quadrature has a time-uniform cell bound and a uniform comparison to
both finite left and midpoint grids. The left-grid error is at most
`g(T)/M + (g(T)+8)/2^p`, where `g(T)=2·3^T·T+3`. The exact one-cell
value gives a uniform bound on every original cofinal observation.
[GaussianBinetWeightedExponentialRowRate](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialRowRate.lean), [GaussianBinetWeightedExponentialUniform](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialUniform.lean), [GaussianBinetWeightedExponentialBound](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialBound.lean), [GaussianBinetWeightedExponentialMidpoint](Lean/IPRADerivations/Analysis/GaussianBinetWeightedExponentialMidpoint.lean).

A literal signed vertical step has the checked quadratic logarithm
estimate. The normalized first-order Stirling expression
`ψ(z)−Log(z)+1/(2z)` has absolute bound `3/(2 Re(z))` at independent
observations.
[GaussianBinetLogVerticalStep](Lean/IPRADerivations/Analysis/GaussianBinetLogVerticalStep.lean), [GaussianBinetStirlingSlopeBound](Lean/IPRADerivations/Analysis/GaussianBinetStirlingSlopeBound.lean).

The actual vertical remainder increment has the first-order term
formed from the literal displacement and the same-clock original
digamma, logarithm and half reciprocal. Exact subtraction cancels the
common Stirling constant. The observation bound retains separate
quadratic log-Gamma and logarithm contributions and normalization
allowances for the original remainder samples.
[GaussianBinetStirlingVerticalAlgebra](Lean/IPRADerivations/Analysis/GaussianBinetStirlingVerticalAlgebra.lean), [GaussianBinetLogGammaVerticalStep](Lean/IPRADerivations/Analysis/GaussianBinetLogGammaVerticalStep.lean), [GaussianBinetStirlingVerticalStep](Lean/IPRADerivations/Analysis/GaussianBinetStirlingVerticalStep.lean).

The literal vertical increments telescope over an internal subdivision.
Positive rescaling identifies the subdivided endpoints with the original
remainder names. If `z = (A ± Bi)/D`, the vertical difference from `R(A/D)`
has leading norm bound `3B/(2A)`. The sharp positive-real anchor gives the
full leading bound `(D+18B)/(12A)` for `R(z)`, with an explicit error at
independent observation clocks.
[GaussianBinetStirlingRescale](Lean/IPRADerivations/Analysis/GaussianBinetStirlingRescale.lean), [GaussianBinetStirlingVerticalRate](Lean/IPRADerivations/Analysis/GaussianBinetStirlingVerticalRate.lean), [GaussianBinetStirlingVerticalGrid](Lean/IPRADerivations/Analysis/GaussianBinetStirlingVerticalGrid.lean), [GaussianBinetStirlingVerticalBound](Lean/IPRADerivations/Analysis/GaussianBinetStirlingVerticalBound.lean).

For the imaginary-axis sine product used in the Binet kernel
identification, the actual finite factor derivative terms give the
literal derivative of the encoded product at any internal cutoff. The
exact first-order expansion uses a primitive recursive second-order
remainder and retains the original sine product at both inputs.
[GaussianSineProductImaginaryLogDerivative](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryLogDerivative.lean), [GaussianSineProductImaginaryFirstOrder](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryFirstOrder.lean).

The imaginary-axis sine-product expansion has a quadratic error
uniform in the cutoff on each bounded interval. The literal row
sum has a quantitative tail and a regular cofinal sampler. Passing
the derivative expansion to the original cofinal sine product keeps
the weighted cofinal derivative term and the exact quadratic rate
with independent observation clocks. The product and reciprocal row
names are invariant under exact rational rescaling.
[GaussianSineProductImaginaryLogDerivativeTail](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryLogDerivativeTail.lean), [GaussianSineProductImaginaryFirstOrderBound](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryFirstOrderBound.lean), [GaussianSineProductImaginaryCofinalDerivative](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryCofinalDerivative.lean), [GaussianSineProductImaginaryScaling](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryScaling.lean).

The original named exponential has a first-order remainder at any
regular small input and an independent quadratic rate for shifts.
Signed rational multiples of the original π name preserve exact
additive increments. Multiplication by the literal imaginary unit
agrees with the actual rotation name used by the sine connection.
[GaussianNamedExponentialLinearRate](Lean/IPRADerivations/Analysis/GaussianNamedExponentialLinearRate.lean), [GaussianNamedExponentialShiftDerivative](Lean/IPRADerivations/Analysis/GaussianNamedExponentialShiftDerivative.lean), [GaussianPiRationalScale](Lean/IPRADerivations/Analysis/GaussianPiRationalScale.lean), [GaussianNamedImaginaryProduct](Lean/IPRADerivations/Analysis/GaussianNamedImaginaryProduct.lean).

At nonnegative rational `x` in a certified bounded interval, the
actual original exponential expression for `sinh(πx)` equals the
product of `πx` and the original cofinal sine product on the imaginary
axis. Positive rescaling preserves the original signed π inputs
exactly. A separate dyadic uniqueness theorem identifies two regular
slope names when their weighted approximants differ quadratically at
the common nonzero step.
[GaussianPiRationalScaleRepresentation](Lean/IPRADerivations/Analysis/GaussianPiRationalScaleRepresentation.lean), [GaussianNamedScaledDerivativeUniqueness](Lean/IPRADerivations/Analysis/GaussianNamedScaledDerivativeUniqueness.lean), [GaussianSineProductImaginaryHyperbolic](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryHyperbolic.lean).

The actual hyperbolic exponential expression has a first-order rate
at a fixed rational base under a positive change of encoding. The
quadratic numerator is uniform as the rational step tends to zero.
The derivative expression equals the original named `π cosh(πx)`.
The original sine product representation has a matching independent
product-rule estimate whose quadratic coefficient is also uniform
under rescaling.
[GaussianNamedDifferenceAlgebra](Lean/IPRADerivations/Analysis/GaussianNamedDifferenceAlgebra.lean), [GaussianPiRationalScaleFactors](Lean/IPRADerivations/Analysis/GaussianPiRationalScaleFactors.lean), [GaussianSineProductImaginaryExponentialShift](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryExponentialShift.lean), [GaussianSineProductImaginaryHyperbolicDerivative](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryHyperbolicDerivative.lean), [GaussianSineProductImaginaryCoshIdentity](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryCoshIdentity.lean), [GaussianSineProductImaginaryHyperbolicProductRuleAlgebra](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryHyperbolicProductRuleAlgebra.lean), [GaussianSineProductImaginaryHyperbolicProductRule](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryHyperbolicProductRule.lean).

At a fixed rational base `x`, the two actual derivative names are
equal by comparison at a common nonzero dyadic displacement. Cancel
the original apart π factor to get `cosh(πx) = P(x)+xD(x)` for the
cofinal sine product `P` and its actual derivative `D`.
[GaussianSineProductImaginaryDerivativeComparison](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryDerivativeComparison.lean), [GaussianSineProductImaginaryCofinalLogDerivative](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryCofinalLogDerivative.lean).

Combining that derivative with the exact hyperbolic sine identity
proves the cleared partial fractions
`(πx) cosh(πx) = sinh(πx) (1+x Σⱼ 2x/(j²+x²))` at the original
rational inputs. This uses the actual cofinal reciprocal row name.
[GaussianSineProductImaginaryCothExpansion](Lean/IPRADerivations/Analysis/GaussianSineProductImaginaryCothExpansion.lean).

At a nonnegative rational time `t`, the cofinal kernel `k(t)` satisfies
`(t/2) cosh(t/2) = sinh(t/2) (1+t² k(t))` with the original exponential
names. Freezing π once at a shared observation binds the literal kernel
rows to the partial-fraction samples. The uniform bounds remove the
freeze and identify the hyperbolic factors at their original time.
[GaussianBinetKernelImaginaryRatioRows](Lean/IPRADerivations/Analysis/GaussianBinetKernelImaginaryRatioRows.lean), [GaussianBinetKernelImaginaryRatioPrefix](Lean/IPRADerivations/Analysis/GaussianBinetKernelImaginaryRatioPrefix.lean), [GaussianBinetKernelImaginaryRatioCofinal](Lean/IPRADerivations/Analysis/GaussianBinetKernelImaginaryRatioCofinal.lean), [GaussianBinetKernelFrozenHyperbolic](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrozenHyperbolic.lean), [GaussianNamedUniformRateClosure](Lean/IPRADerivations/Analysis/GaussianNamedUniformRateClosure.lean), [GaussianBinetKernelRationalTimeCleared](Lean/IPRADerivations/Analysis/GaussianBinetKernelRationalTimeCleared.lean).

For positive rational time the original hyperbolic sine is apart from zero.
Its actual Taylor series gives a quantitative lower bound from the first
odd term. Cancelling the original denominator yields
`k(t) = ((t/2) cosh(t/2)−sinh(t/2))/(t² sinh(t/2))` with the actual
reciprocal sampler. At zero the original kernel equals `1/12`.
[GaussianBinetKernelSinhOddLower](Lean/IPRADerivations/Analysis/GaussianBinetKernelSinhOddLower.lean), [GaussianBinetKernelSinhApartness](Lean/IPRADerivations/Analysis/GaussianBinetKernelSinhApartness.lean), [GaussianNamedClearedScalarQuotient](Lean/IPRADerivations/Analysis/GaussianNamedClearedScalarQuotient.lean), [GaussianBinetKernelElementaryRational](Lean/IPRADerivations/Analysis/GaussianBinetKernelElementaryRational.lean).

Multiplying the cleared kernel identity by the original negative
half-time exponential identifies `(1−exp(−t))k(t)` with the actual
cofinal quadrature of `(1/2−u)exp(−tu)` on `[0,1]`. The positive
branch cancels an exact nonzero rational scale. At `t = 0` the
weighted grid bound proves exact agreement and regularity.
[GaussianBinetKernelHalfExponential](Lean/IPRADerivations/Analysis/GaussianBinetKernelHalfExponential.lean), [GaussianBinetKernelWeightedBridge](Lean/IPRADerivations/Analysis/GaussianBinetKernelWeightedBridge.lean), [GaussianBinetKernelWeightedBridgeZero](Lean/IPRADerivations/Analysis/GaussianBinetKernelWeightedBridgeZero.lean).

On each bounded rational time panel, the original exponential
at `−(z+1)t` equals the product of the original names at `−zt` and
`−t`. The actual integrand difference across `z` and `z+1` therefore
equals the original `exp(−zt)` times the cofinal weighted exponential
unit quadrature. This applies to any admitted radii for the two
original integrands and includes time zero.
[GaussianBinetLaplaceExponentialShift](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceExponentialShift.lean), [GaussianBinetLaplaceIntegrandShift](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceIntegrandShift.lean), [GaussianBinetLaplaceWeightedShiftRow](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceWeightedShiftRow.lean).

The Binet kernel series uses the original named π in each positive row
`2/(t²+4π²n²)`. On `0 ≤ t ≤ T` the actual finite and cofinal samples
are bounded below by `2/(T²+100)` at positive cutoffs. The row majorant
`1/(8n²)` gives the uniform leading tail bound `1/(8N)` for every
positive cutoff `N`. The comparison of the original finite and cofinal
evaluators retains independent dyadic errors. Both evaluators satisfy
the cutoff-independent Lipschitz estimate with gain `T` on `[0,T]`,
including its uniform-mesh specialization.
[GaussianBinetKernelPi](Lean/IPRADerivations/Analysis/GaussianBinetKernelPi.lean), [GaussianBinetKernelRows](Lean/IPRADerivations/Analysis/GaussianBinetKernelRows.lean), [GaussianBinetKernelPositive](Lean/IPRADerivations/Analysis/GaussianBinetKernelPositive.lean), [GaussianBinetKernelTailMajorant](Lean/IPRADerivations/Analysis/GaussianBinetKernelTailMajorant.lean), [GaussianBinetKernelTail](Lean/IPRADerivations/Analysis/GaussianBinetKernelTail.lean), [GaussianBinetKernelCofinal](Lean/IPRADerivations/Analysis/GaussianBinetKernelCofinal.lean), [GaussianBinetKernelTimeContinuity](Lean/IPRADerivations/Analysis/GaussianBinetKernelTimeContinuity.lean).

The literal reciprocal-square sum satisfies the Basel identity against
the original zeta and π names. Rewriting each actual zero-parameter
kernel row by that sum identifies the cofinal kernel at zero with
`1/12` for every positive denominator encoding. The exact finite row
order gives the global upper bound `k(t) ≤ 1/12` for nonnegative rational
`t`. A sample at clock `p` obeys the upper bound `1/12 + 2⁻ᵖ`.
[GaussianBinetBaselBinding](Lean/IPRADerivations/Analysis/GaussianBinetBaselBinding.lean), [GaussianBinetBaselName](Lean/IPRADerivations/Analysis/GaussianBinetBaselName.lean), [GaussianBinetKernelZero](Lean/IPRADerivations/Analysis/GaussianBinetKernelZero.lean), [GaussianBinetKernelUpper](Lean/IPRADerivations/Analysis/GaussianBinetKernelUpper.lean).

On a certified finite strip the original Gaussian exponential is
evaluated at the exact argument `−zt`. Its normalized product with
the kernel samples gives the finite and cofinal Binet integrands.
The independent observation comparison with the finite cutoff has
leading error `1/(8N)`. The integrand has a computable Lipschitz gain
uniform in the cutoff on each finite strip and a finite mesh bound.
[GaussianBinetKernelCoarseBound](Lean/IPRADerivations/Analysis/GaussianBinetKernelCoarseBound.lean), [GaussianBinetLaplaceExponential](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceExponential.lean), [GaussianBinetLaplaceIntegrand](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceIntegrand.lean).

The original integrands yield regular compact quadrature names on
any admitted finite panel in nonnegative time. The translated chart
reads each tag at its exact physical rational time, including zero.
The arbitrary grid-refinement and same-grid cutoff comparisons give
the named compact truncation estimate with leading error
`(panel width)/(8N)` at independent observation clocks.
Changing the certified disk radius or time horizon preserves the actual
integrand at each physical tag and preserves the compact name for the
same panel.
[GaussianBinetLaplaceStrip](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStrip.lean), [GaussianBinetLaplaceStripCutoff](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStripCutoff.lean), [GaussianBinetLaplaceStripHorizon](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStripHorizon.lean).

The squared norm of the actual complex exponential at `−zt` agrees
with the square of the original real decay at `−Re(z)t`. The observation
norm estimate transfers that decay to the actual normalized product
with the kernel. The majorant retains the leading coefficient `1/12`
and explicit errors at the original product and real decay clocks.
[GaussianBinetLaplaceDecay](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceDecay.lean), [GaussianBinetLaplaceDomination](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceDomination.lean).

The compact tail after a rational endpoint is bounded uniformly in
the strip width and the certified horizon. The original nonnegative
real decay sample at the starting endpoint supplies the sharp leading
coefficient `1/(12 Re(z))`, with explicit independent observation
errors. At physical cutoff `D L`, an effective envelope gives leading
bound `D 2⁻ᴸ/(12 X)` for `Re(z)=X/D`. A zero-width strip evaluates
exactly to zero.
[GaussianBinetLaplaceScalarMajorant](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceScalarMajorant.lean), [GaussianBinetLaplaceStripDomination](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStripDomination.lean), [GaussianBinetLaplaceStripTail](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStripTail.lean), [GaussianBinetLaplaceStripTailEnvelope](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceStripTailEnvelope.lean), [GaussianBinetLaplaceSharpTail](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceSharpTail.lean).

The original compact quadrature is additive at a physical split.
The prefix comparison retains the effective leading tail
`D 2⁻ᴸ/(12 X)` at independent clocks for a prefix ending at `D L`.
This also compares two actual exhaustion prefixes at their own
horizons and covers equality of cutoffs.
[GaussianBinetLaplaceExhaustion](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceExhaustion.lean), [GaussianBinetLaplaceOrderedPrefixes](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceOrderedPrefixes.lean).

The improper Binet Laplace name reads the actual compact quadrature
at an internal cutoff and a later clock. It is regular on each
certified signed rational right-half-plane chart. Its observations
compare to those of every positive finite prefix with the same
leading bound `D 2⁻ᴸ/(12 X)`.
[GaussianBinetLaplaceImproperName](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceImproperName.lean).

The original real decay at time zero evaluates exactly to one. The
finite decay quadrature includes the zero left cell with the same
error bound. The actual improper Binet sampler consequently has
norm at most `1/(12 Re(z)) + 2⁻⁽ᵖ⁺¹⁾` at its observation clock `p`.
[GaussianEulerDecayQuadratureAtZero](Lean/IPRADerivations/Analysis/GaussianEulerDecayQuadratureAtZero.lean), [GaussianBinetLaplaceImproperBound](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceImproperBound.lean).

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
[GaussianCompactPointwiseDifference](Lean/IPRADerivations/Analysis/GaussianCompactPointwiseDifference.lean), [GaussianCompactDifferenceRefinement](Lean/IPRADerivations/Analysis/GaussianCompactDifferenceRefinement.lean), [GaussianBinetLaplaceDifferencePrefix](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceDifferencePrefix.lean), [GaussianBinetLaplaceDifferenceGrid](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceDifferenceGrid.lean).

For the original finite exponential rectangle, interchanging the two
sums leaves the actual serialized weights and observations in place.
The complex exponential columns telescope to their original endpoint
expression, and their tails decay on the selected horizon. At the
prescribed finite budgets, the rectangle is within `2/2^p` of the
literal weighted-resolvent grid. The cofinal comparison binds its
limit to the canonical Stirling unit difference.
[GaussianBinetExponentialPanel](Lean/IPRADerivations/Analysis/GaussianBinetExponentialPanel.lean), [GaussianBinetExponentialIntegralGrid](Lean/IPRADerivations/Analysis/GaussianBinetExponentialIntegralGrid.lean), [GaussianBinetExponentialIntegral](Lean/IPRADerivations/Analysis/GaussianBinetExponentialIntegral.lean), [GaussianBinetExponentialRectangle](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangle.lean), [GaussianBinetExponentialRectangleShift](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangleShift.lean), [GaussianBinetExponentialRectangleColumn](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangleColumn.lean), [GaussianBinetExponentialRectangleEndpoint](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangleEndpoint.lean), [GaussianBinetExponentialRectangleResolvent](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangleResolvent.lean), [GaussianBinetExponentialRectangleEvaluation](Lean/IPRADerivations/Analysis/GaussianBinetExponentialRectangleEvaluation.lean).

The normalized discrepancy `R(z+j)−J(z+j)` uses the actual remainder and
actual improper Binet names. Its bound decays uniformly as the internal
shift `j` grows, with a separate dyadic observation allowance. An adjacent
equality proof would make that family constant and hence zero. The closed
conditional derives the first Binet identity from the hypothesis that the
actual unit difference of `J` equals the weighted-resolvent quadrature
along the entire translated family.
[GaussianNamedRecurrencePinning](Lean/IPRADerivations/Analysis/GaussianNamedRecurrencePinning.lean), [GaussianNamedDifferenceZero](Lean/IPRADerivations/Analysis/GaussianNamedDifferenceZero.lean), [GaussianBinetFirstFormulaDecay](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormulaDecay.lean), [GaussianBinetFirstFormulaPinning](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormulaPinning.lean).

The first Binet formula is proved for the two original names at every
encoded complex rational point in the right half-plane. At each requested
precision, one explicit horizon, clock, and pair of meshes satisfy both
sides of the rectangle comparison. Their bound identifies the actual
unit difference of the improper sampler with the weighted resolvent.
The translated discrepancy argument then proves equality of the
Stirling remainder and the original improper integral. The closed
theorem has only the original input-domain guard.
[GaussianNamedProductObservationBound](Lean/IPRADerivations/Analysis/GaussianNamedProductObservationBound.lean), [GaussianBinetLaplaceWeightedGridReadback](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceWeightedGridReadback.lean), [GaussianBinetLaplaceWeightedGridProduct](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceWeightedGridProduct.lean), [GaussianBinetLaplaceWeightedGridRectangle](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceWeightedGridRectangle.lean), [GaussianBinetLaplaceRectangleRowBudget](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceRectangleRowBudget.lean), [GaussianBinetLaplaceRectangleSchedule](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceRectangleSchedule.lean), [GaussianBinetLaplaceRectangleJoin](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceRectangleJoin.lean), [GaussianBinetFirstFormula](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormula.lean).

On a common right-half-plane margin and disk, the original rational
Stirling remainder has an explicit linear rate. Transferring it to
the original improper Laplace sampler gives a regular named lift
with a quantitative readback at late rational observations. A
single late rational observation identifies the lift with the
Stirling remainder assembled from the original named log-Gamma,
logarithm, argument and Stirling constant.
[GaussianRightHalfPlaneLogarithmCompactBound](Lean/IPRADerivations/Analysis/GaussianRightHalfPlaneLogarithmCompactBound.lean), [GaussianBinetStirlingRemainderRate](Lean/IPRADerivations/Analysis/GaussianBinetStirlingRemainderRate.lean), [GaussianBinetLaplaceNamed](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceNamed.lean), [GaussianBinetFirstFormulaNamed](Lean/IPRADerivations/Analysis/GaussianBinetFirstFormulaNamed.lean).

For the second Binet formula, the original rational integrand
`z/(z²+u²)` equals the average of the two resolvents at `z±iu` on the
right half-plane. The admitted poles have the same positive-real
margin. The resulting original compact arctangent quadrature is
regular, and every actual observation at time `t` has norm bounded
by `t/Re(z)`.
[GaussianBinetArctangentResolvent](Lean/IPRADerivations/Analysis/GaussianBinetArctangentResolvent.lean), [GaussianBinetArctangentResolventRate](Lean/IPRADerivations/Analysis/GaussianBinetArctangentResolventRate.lean), [GaussianBinetArctangentQuadrature](Lean/IPRADerivations/Analysis/GaussianBinetArctangentQuadrature.lean), [GaussianBinetArctangentQuadratureBound](Lean/IPRADerivations/Analysis/GaussianBinetArctangentQuadratureBound.lean).

The two original exponential panel sums at the signed poles read back
on one common horizon. Their symmetric average approximates the exact
cosine resolvent uniformly over a bounded rational frequency interval,
with explicit finite-mesh and exponential-tail errors.
[GaussianBinetArctangentSignedPole](Lean/IPRADerivations/Analysis/GaussianBinetArctangentSignedPole.lean), [GaussianBinetArctangentPoleLaplace](Lean/IPRADerivations/Analysis/GaussianBinetArctangentPoleLaplace.lean), [GaussianBinetArctangentCosineLaplace](Lean/IPRADerivations/Analysis/GaussianBinetArctangentCosineLaplace.lean).

The original pure-imaginary exponential quadrature satisfies the
cleared finite antiderivative with both frequency signs, including
zero. The difference of the original signed-pole Laplace panels
approximates the cleared sine resolvent with uniform bounds on the
bounded frequency interval.
[GaussianBinetImaginaryExponentialIntegral](Lean/IPRADerivations/Analysis/GaussianBinetImaginaryExponentialIntegral.lean), [GaussianBinetSineLaplaceResolvent](Lean/IPRADerivations/Analysis/GaussianBinetSineLaplaceResolvent.lean).

On a common grid, the original finite arctangent quadrature compares
with the original rectangle of cosine transforms. The outer grid
multiplies the uniform resolvent error by its physical width. Each
actual shifted exponential factors with explicit error into the
original damping and the purely imaginary oscillatory sample.
[GaussianBinetArctangentCosineRectangle](Lean/IPRADerivations/Analysis/GaussianBinetArctangentCosineRectangle.lean), [GaussianBinetOscillatoryPanelFactor](Lean/IPRADerivations/Analysis/GaussianBinetOscillatoryPanelFactor.lean).

The actual positive Pi-scaled exponential has a Taylor gap from one
of at least `4t` at every positive rational time. Its reciprocal is
regular and has norm at most `1/(4t)` at every observation. The
original arctangent times this reciprocal has norm at most
`1/(4 Re(z))` all the way toward the origin. For an exact rational
inverse pair `xy = 1`, the literal geometric power sum has the
cleared finite identity `(x−1) Σ_{j=1}^N y^j = 1−y^N`.
[GaussianExponentialAffineLower](Lean/IPRADerivations/Analysis/GaussianExponentialAffineLower.lean), [GaussianBinetBoseExponential](Lean/IPRADerivations/Analysis/GaussianBinetBoseExponential.lean), [GaussianBinetBoseDenominator](Lean/IPRADerivations/Analysis/GaussianBinetBoseDenominator.lean), [GaussianBinetBoseIntegrandBound](Lean/IPRADerivations/Analysis/GaussianBinetBoseIntegrandBound.lean), [GaussianRationalInverseGeometric](Lean/IPRADerivations/Analysis/GaussianRationalInverseGeometric.lean).

The original finite cosine rectangle equals the transposed sum with
both literal mesh weights. The transposed entries have an explicit
comparison to the original damping multiplied by the mean of the
two imaginary exponentials. Exact signed rational rescaling binds
their frequency charts at the actual grid tags.
[GaussianRationalQuadratureMean](Lean/IPRADerivations/Analysis/GaussianRationalQuadratureMean.lean), [GaussianBinetOscillatoryRectangleTranspose](Lean/IPRADerivations/Analysis/GaussianBinetOscillatoryRectangleTranspose.lean), [GaussianBinetOscillatoryMatrixCell](Lean/IPRADerivations/Analysis/GaussianBinetOscillatoryMatrixCell.lean), [GaussianBinetImaginaryExponentialScale](Lean/IPRADerivations/Analysis/GaussianBinetImaginaryExponentialScale.lean).

At every original arctangent observation, the leading term is
`t/z` with norm error at most `(t/Re(z))³`. The original rational
rows retain their exact values, so this bound has no sampling
allowance. For positive rational time the divided arctangent
differs from `1/z` by at most `t²/Re(z)³`.
[GaussianBinetArctangentLinearApproximation](Lean/IPRADerivations/Analysis/GaussianBinetArctangentLinearApproximation.lean).

Read the positive exponential sample selected by the actual Bose
reciprocal. The exact inverse of that exponential sample has norm
at most `1/(1+4t)`. For `t=A/B>0` its literal geometric prefix of
length `N` differs from the original reciprocal observation by
at most `B²/[4A(B+4NA)]`, independently of the observation clock.
[GaussianBinetBoseGeometricRatio](Lean/IPRADerivations/Analysis/GaussianBinetBoseGeometricRatio.lean), [GaussianRationalGeometricPowerTail](Lean/IPRADerivations/Analysis/GaussianRationalGeometricPowerTail.lean), [GaussianBinetBoseSeries](Lean/IPRADerivations/Analysis/GaussianBinetBoseSeries.lean).

The literal arctangent-decay row admits a common half-decay majorant
with an explicit clock allowance, including at time zero. The rescaled
zero-start scalar quadrature yields the bound `11K/m²` for row `m`
on every integer horizon with the verified mesh and clock budgets.
A shared grid and one frozen Pi sample give the actual tail bound
`11K/C` for every finite block after row `C`.
[GaussianBinetSecondDecayEnvelope](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayEnvelope.lean), [GaussianBinetSecondDecayPointwise](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayPointwise.lean), [GaussianBinetSecondDecayQuadrature](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayQuadrature.lean), [GaussianBinetSecondDecayGrid](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayGrid.lean), [GaussianBinetSecondDecayFinite](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayFinite.lean), [GaussianBinetSecondDecayTail](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayTail.lean), [GaussianBinetSecondDecayFrozenTail](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayFrozenTail.lean).

The original unscaled second Binet integrand has the continuous
endpoint `1/(2π z)` at zero. The denominator's original observation
keeps its own Pi sample and has quadratic error from the linear
term at that clock. Comparing with the original divided arctangent
gives leading error `(K³+100K)t` for `0<t≤1/10` and
`1/Re(z)≤K`, with independent observation errors.
[GaussianBinetBoseLinearApproximation](Lean/IPRADerivations/Analysis/GaussianBinetBoseLinearApproximation.lean), [GaussianBinetBoseIntegrandEndpoint](Lean/IPRADerivations/Analysis/GaussianBinetBoseIntegrandEndpoint.lean).

The original signed Pi-scaled decay row compares with the actual
frozen-Pi decay evaluator on the same compact time interval. Its
rate is uniform in the encoded rational tag and therefore works
across every later time mesh. The product rate also applies to
the original arctangent-weighted rows.
[GaussianBinetSecondDecayPiBridge](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayPiBridge.lean).

At each positive rational time, the corresponding original signed
exponential rows approximate the powers of the actual geometric ratio.
Their literal finite sums give a regular cofinal evaluator. Its normalized
samples read back the exact finite prefix and differ from the reciprocal
of the original Bose denominator by at most `6/2^p`. The object theory
proves equivalence of the two names.
[GaussianBinetBoseIntegerScale](Lean/IPRADerivations/Analysis/GaussianBinetBoseIntegerScale.lean), [GaussianBinetBoseSeriesRows](Lean/IPRADerivations/Analysis/GaussianBinetBoseSeriesRows.lean), [GaussianBinetBoseLiteralPrefix](Lean/IPRADerivations/Analysis/GaussianBinetBoseLiteralPrefix.lean), [GaussianBinetBoseLiteralCofinal](Lean/IPRADerivations/Analysis/GaussianBinetBoseLiteralCofinal.lean)

The original transposed cosine columns approximate the sine
quotient on the same mesh. At positive time the cleared cosine
antiderivative gives the quotient by the imaginary frequency. At
zero the regularized quotient has its exact removable value. A
single primitive-recursive row inherits uniform norm and mesh bounds.
[GaussianBinetCosinePrimitive](Lean/IPRADerivations/Analysis/GaussianBinetCosinePrimitive.lean), [GaussianBinetOscillatoryColumns](Lean/IPRADerivations/Analysis/GaussianBinetOscillatoryColumns.lean), [GaussianBinetOscillatorySineQuotient](Lean/IPRADerivations/Analysis/GaussianBinetOscillatorySineQuotient.lean), [GaussianBinetOscillatoryZeroColumn](Lean/IPRADerivations/Analysis/GaussianBinetOscillatoryZeroColumn.lean), [GaussianBinetOscillatorySineRows](Lean/IPRADerivations/Analysis/GaussianBinetOscillatorySineRows.lean)

Summing the regularized sine columns with the original time weight
gives a finite damped sine integral. It approximates both the original
finite arctangent quadrature and the original arctangent observations,
with explicit mesh, horizon and clock errors.
[GaussianBinetOscillatorySineRectangle](Lean/IPRADerivations/Analysis/GaussianBinetOscillatorySineRectangle.lean), [GaussianBinetArctangentSineGridComparison](Lean/IPRADerivations/Analysis/GaussianBinetArctangentSineGridComparison.lean)

The original second Binet product admits a compact integral on every
positive rational interval `[A/E,(A+C)/E]`. The original arctangent
and reciprocal have time rates on that interval, so the literal
left quadrature defines a regular name. Every actual sample has
norm at most `CD/(4EX)` for real part `X/D`, including intervals
whose lower endpoint tends to zero.
[GaussianBinetBoseReciprocalTimeRate](Lean/IPRADerivations/Analysis/GaussianBinetBoseReciprocalTimeRate.lean), [GaussianBinetArctangentTimeRate](Lean/IPRADerivations/Analysis/GaussianBinetArctangentTimeRate.lean), [GaussianBinetBoseCompact](Lean/IPRADerivations/Analysis/GaussianBinetBoseCompact.lean), [GaussianBinetBoseCompactBound](Lean/IPRADerivations/Analysis/GaussianBinetBoseCompactBound.lean)

At each positive frozen Pi frequency, the exact shifted exponential
panels compare to the standard real damping times the original
regularized sine quotient. Summing on the shared mesh gives the
actual Binet kernel row, up to explicit mesh, horizon and clock
errors. Independent radii and clocks for the same positive sine
quotient have a separate quantitative comparison.
[GaussianBinetSineDampedTransform](Lean/IPRADerivations/Analysis/GaussianBinetSineDampedTransform.lean), [GaussianBinetSineFrozenPiTerm](Lean/IPRADerivations/Analysis/GaussianBinetSineFrozenPiTerm.lean), [GaussianBinetSineDampedAxis](Lean/IPRADerivations/Analysis/GaussianBinetSineDampedAxis.lean), [GaussianBinetSineDampedPanels](Lean/IPRADerivations/Analysis/GaussianBinetSineDampedPanels.lean), [GaussianBinetSineRealDampedPanels](Lean/IPRADerivations/Analysis/GaussianBinetSineRealDampedPanels.lean), [GaussianBinetSineDampedQuadrature](Lean/IPRADerivations/Analysis/GaussianBinetSineDampedQuadrature.lean), [GaussianBinetSineQuotientClock](Lean/IPRADerivations/Analysis/GaussianBinetSineQuotientClock.lean)

A single frozen Pi clock supplies every literal reciprocal row. The truncated kernel and the actual exponential-weighted prefix compare with the cofinal kernel and the original first Binet Laplace integrand, with quantitative cutoff and clock budgets.
[GaussianBinetKernelFrozenPrefix](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrozenPrefix.lean)

Exact compact rescaling and additivity compare the original intervals whose lower endpoints are dyadic. The omitted strip has norm at most its width divided by four times the real part. The resulting regular name integrates the original product from zero to each positive integer horizon.
[GaussianBinetBoseCompactAlignment](Lean/IPRADerivations/Analysis/GaussianBinetBoseCompactAlignment.lean), [GaussianBinetBoseOriginExhaustion](Lean/IPRADerivations/Analysis/GaussianBinetBoseOriginExhaustion.lean), [GaussianBinetBoseOriginName](Lean/IPRADerivations/Analysis/GaussianBinetBoseOriginName.lean)

The original exponential-minus-one observation retains a cubic Taylor lower bound. The arctangent times the original reciprocal is bounded by K/t² when D≤KX. Its actual compact integral on [A/E,(A+C)/E] is bounded by 2KE/A with an explicit sample allowance, independently of the upper endpoint.
[GaussianBinetBoseCubicGap](Lean/IPRADerivations/Analysis/GaussianBinetBoseCubicGap.lean), [GaussianBinetBoseFarBound](Lean/IPRADerivations/Analysis/GaussianBinetBoseFarBound.lean), [GaussianBinetBoseFarQuadrature](Lean/IPRADerivations/Analysis/GaussianBinetBoseFarQuadrature.lean)

The time margin E·t≥1 permits a common cutoff N≥E²·2^p. Each original arctangent-weighted cell of that literal prefix compares with its frozen Pi counterpart, with a common error 5KT/2^p over t≤T when D≤KX.
[GaussianBinetBoseLiteralUniform](Lean/IPRADerivations/Analysis/GaussianBinetBoseLiteralUniform.lean), [GaussianBinetBoseLiteralFrozen](Lean/IPRADerivations/Analysis/GaussianBinetBoseLiteralFrozen.lean)

The actual finite frozen-Pi prefixes of lengths C+r and C are compared at the same supplied time mesh and observation clock. The explicit certified mesh and clock floors give the uniform tail 11K/C.
[GaussianBinetSecondDecaySharedTail](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecaySharedTail.lean)

The actual shifted exponential antiderivative uses the rate-versus-horizon inequality directly. A common physical horizon independent of the Pi denominator now suffices to compare the actual weighted sine quadrature to each literal Binet kernel row.
[GaussianBinetFixedHorizonDecay](Lean/IPRADerivations/Analysis/GaussianBinetFixedHorizonDecay.lean), [GaussianBinetFixedHorizonPole](Lean/IPRADerivations/Analysis/GaussianBinetFixedHorizonPole.lean), [GaussianBinetFixedHorizonSine](Lean/IPRADerivations/Analysis/GaussianBinetFixedHorizonSine.lean), [GaussianBinetFixedHorizonFrozenRows](Lean/IPRADerivations/Analysis/GaussianBinetFixedHorizonFrozenRows.lean)

Both cutoff limits now give the original improper integral as a regular name on the encoded rational right half-plane. At independent clocks its comparison to the original compact interval [2^(-L-1),T] has leading error 2K/T + D/(4X·2^(L+1)) when D≤KX.
[GaussianBinetBoseHorizonRate](Lean/IPRADerivations/Analysis/GaussianBinetBoseHorizonRate.lean), [GaussianBinetBoseImproperName](Lean/IPRADerivations/Analysis/GaussianBinetBoseImproperName.lean)

The original compact product compares with the literal exponential prefix on any certified refinement. The angular precision and cutoff may be chosen before the mesh, so the same positive time tags can be used for later decay rows.
[GaussianBinetBosePrefixQuadrature](Lean/IPRADerivations/Analysis/GaussianBinetBosePrefixQuadrature.lean), [GaussianBinetBosePrefixRefinement](Lean/IPRADerivations/Analysis/GaussianBinetBosePrefixRefinement.lean)

The actual arctangent-weighted quadrature expands to a finite matrix and transposes with the original time weight. Each cell retains the exact signed exponential and its original time-tag-dependent observation clock.
[GaussianBinetBosePrefixTranspose](Lean/IPRADerivations/Analysis/GaussianBinetBosePrefixTranspose.lean)

The normalized factor of two preserves the original improper name with twice the compact-cutoff error. A comparison with the first Binet integral suffices for the second identity. The positive weighted cells agree exactly with the original sine transform cells, and the zero-frequency cell has its removable value.
[GaussianBinetSecondFormulaReduction](Lean/IPRADerivations/Analysis/GaussianBinetSecondFormulaReduction.lean), [GaussianBinetSecondRowCell](Lean/IPRADerivations/Analysis/GaussianBinetSecondRowCell.lean)

A single sine clock, horizon and grid count give error 10/2^p between the original arctangent observation and its actual damped sine rectangle for all encoded time tags bounded by the chosen horizon.
[GaussianBinetArctangentSineUniform](Lean/IPRADerivations/Analysis/GaussianBinetArctangentSineUniform.lean)

The literal transposed prefix compares with the frozen-Pi matrix at a separately chosen later observation clock. Each frozen column is the exact geometric row, and the zero-start matrix binds to the existing shared-mesh tail.
[GaussianBinetBoseFrozenMatrix](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenMatrix.lean), [GaussianBinetBoseFrozenOrigin](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenOrigin.lean)

The original removable column and an explicit sine quotient bound control the discarded low-frequency prefix. Every remaining frequency has an explicit positive margin, so the fixed-horizon sine transform uses a tail bound independent of raw denominator size.
[GaussianBinetFixedHorizonPositiveMargin](Lean/IPRADerivations/Analysis/GaussianBinetFixedHorizonPositiveMargin.lean), [GaussianBinetSineQuotientMajorant](Lean/IPRADerivations/Analysis/GaussianBinetSineQuotientMajorant.lean), [GaussianBinetSineStripCut](Lean/IPRADerivations/Analysis/GaussianBinetSineStripCut.lean), [GaussianBinetOscillatorySineSmallStrip](Lean/IPRADerivations/Analysis/GaussianBinetOscillatorySineSmallStrip.lean)

The literal first Binet Laplace strip and the shared-Pi finite kernel prefix use exactly the same physical tags and left weights. Their explicit cutoff bound is 14 times the physical width divided by 2^p.
[GaussianBinetKernelFrozenStrip](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrozenStrip.lean)

The original cofinal Laplace integrand has norm at most one half. Each compact left sum is bounded by half the physical width, and exact additivity gives the same leading error for the removed left interval at independent clocks.
[GaussianBinetLaplaceLowerWindow](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceLowerWindow.lean)

The original frozen decay observation is moved to the exact sine evaluation clock. Replacing the original arctangent by the scheduled sine rectangle on that same grid has error T*(20+2KT)/2^q, including the original time-zero tag.
[GaussianBinetSecondWeightedSinePoint](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSinePoint.lean), [GaussianBinetSecondWeightedSineGrid](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineGrid.lean)

The exact zero-start frozen matrix equals the original finite geometric row sum. Its scheduled sine replacement has error at most NT(20+2KT)/2^q for N rows on the same physical mesh and with the same frozen Pi sample.
[GaussianBinetSecondWeightedSinePrefix](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSinePrefix.lean)

The weighted sine column can be evaluated at the sine rectangle clock even when the antiderivative uses a later mesh clock. The comparison to the frozen kernel row separates the dyadic clock error from the endpoint error controlled by the positive frequency margin.
[GaussianBinetSineDampedRetiming](Lean/IPRADerivations/Analysis/GaussianBinetSineDampedRetiming.lean), [GaussianBinetSineKernelCommonClock](Lean/IPRADerivations/Analysis/GaussianBinetSineKernelCommonClock.lean)

The literal frozen Pi prefix uses an explicit size-dependent tail independent of observation precision. The original positive frequency tags and integration weight read back exactly, and the literal late damping clock can be chosen independently of the Pi clock.
[GaussianBinetKernelFrozenIndependent](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrozenIndependent.lean), [GaussianBinetKernelFrequencyGrid](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrequencyGrid.lean)

The original tags of the compact interval from 1/E to T match the corresponding suffix of the complete frozen time grid. The mesh weights agree exactly, and the time-tag comparison retains a uniform dyadic allowance.
[GaussianBinetBoseFrozenTimeRescale](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenTimeRescale.lean), [GaussianBinetBoseFrozenSuffix](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenSuffix.lean)

The original positive row majorant controls the geometric tail before the omitted zero-start time cells are restored. The combined error is 11K/I + 2KI/E², independent of the discarded geometric count.
[GaussianRationalSuffixMask](Lean/IPRADerivations/Analysis/GaussianRationalSuffixMask.lean), [GaussianBinetSecondDecaySuffixBound](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecaySuffixBound.lean), [GaussianBinetBoseFrozenSuffixCut](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenSuffixCut.lean), [GaussianBinetBoseFrozenOriginCut](Lean/IPRADerivations/Analysis/GaussianBinetBoseFrozenOriginCut.lean)

Exact finite interchange exposes each positive transposed column as the original complex damping times the original real-damped sine quadrature. The physical floor cut and low-frequency error hold on that same grid.
[GaussianBinetSecondWeightedSineMatrix](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineMatrix.lean), [GaussianBinetSecondWeightedSineTranspose](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineTranspose.lean), [GaussianBinetSecondWeightedSineSuffix](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineSuffix.lean), [GaussianBinetSecondWeightedSineCut](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineCut.lean)

Compare the literal positive sine suffix with the original first Binet improper observation via its arbitrary-mesh compact quadrature. The per-tag comparison permits different certified damping radii.
[GaussianBinetKernelFrequencyRadius](Lean/IPRADerivations/Analysis/GaussianBinetKernelFrequencyRadius.lean), [GaussianBinetLaplaceFrequencySuffix](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceFrequencySuffix.lean)

Checked the later frozen prefix against the weighted sine prefix on the same time grid, with an independent angular clock. The retained angular cells compare to the original frozen kernel with separately bounded observation and time-tail errors.
[GaussianBinetSecondDecayRetiming](Lean/IPRADerivations/Analysis/GaussianBinetSecondDecayRetiming.lean), [GaussianBinetSineKernelFrequency](Lean/IPRADerivations/Analysis/GaussianBinetSineKernelFrequency.lean)

The compact comparison fixes the retained geometric count before choosing the literal observation clock. Refinement, freezing, suffix alignment, and the origin correction connect the original improper sample to the retained full frozen matrix with error at most 9·2^-h.
[GaussianBinetBoseLiteralLate](Lean/IPRADerivations/Analysis/GaussianBinetBoseLiteralLate.lean), [GaussianBinetBosePrefixRefinementLate](Lean/IPRADerivations/Analysis/GaussianBinetBosePrefixRefinementLate.lean), [GaussianBinetBoseImproperFrozen](Lean/IPRADerivations/Analysis/GaussianBinetBoseImproperFrozen.lean)

Explicit primitive-recursive schedules choose the time, geometric, and strip cutoffs, then pay independent angular, kernel, and Laplace sample budgets on one dyadic denominator.
[GaussianBinetSecondEarlySchedule](Lean/IPRADerivations/Analysis/GaussianBinetSecondEarlySchedule.lean), [GaussianBinetSecondFrequencySchedule](Lean/IPRADerivations/Analysis/GaussianBinetSecondFrequencySchedule.lean), [GaussianBinetSecondErrorBudget](Lean/IPRADerivations/Analysis/GaussianBinetSecondErrorBudget.lean)

The checked late Bose schedule admits independent lower bounds on π accuracy, the time mesh, and the final literal clock. The retained sine prefix is transposed and compared with the exact frozen kernel rectangle. Its frequency columns approximate the original first-Binet quadrature using the original mesh weight.
[GaussianBinetBoseLateSchedule](Lean/IPRADerivations/Analysis/GaussianBinetBoseLateSchedule.lean), [GaussianBinetSecondWeightedSineTransposedPrefix](Lean/IPRADerivations/Analysis/GaussianBinetSecondWeightedSineTransposedPrefix.lean), [GaussianBinetFrozenKernelRectangle](Lean/IPRADerivations/Analysis/GaussianBinetFrozenKernelRectangle.lean), [GaussianBinetSineKernelGrid](Lean/IPRADerivations/Analysis/GaussianBinetSineKernelGrid.lean), [GaussianBinetSineKernelPrefix](Lean/IPRADerivations/Analysis/GaussianBinetSineKernelPrefix.lean), [GaussianBinetFrozenKernelLaplace](Lean/IPRADerivations/Analysis/GaussianBinetFrozenKernelLaplace.lean)

The actual first and scaled second improper observations differ by at most 35·2^-p at every common observation p. The checked first Binet identity identifies the scaled original Bose sampler with the original Stirling remainder. The object-theory theorem is universally closed.
[GaussianBinetSecondFormula](Lean/IPRADerivations/Analysis/GaussianBinetSecondFormula.lean)

The lifted program reads the original scaled Bose sampler at each selected rational argument. It is regular, admits an independent comparison to every sufficiently late rational observation, and is equivalent to the original named Stirling remainder on the certified right half-plane.
[GaussianNamedRightHalfPlaneLiftTransport](Lean/IPRADerivations/Analysis/GaussianNamedRightHalfPlaneLiftTransport.lean), [GaussianBinetSecondFormulaNamed](Lean/IPRADerivations/Analysis/GaussianBinetSecondFormulaNamed.lean)

The actual compact quadratures on adjacent unit intervals differ by the original logarithm quadrature with error at most 8·2^-p at the common observation clock, on every positive mesh. The upper and lower unit integrals use the same physical tags.
[GaussianRaabeUnitGridRecurrence](Lean/IPRADerivations/Analysis/GaussianRaabeUnitGridRecurrence.lean)

A checked regular point evaluator uses the original positive-time Euler power and the reciprocal of the unscaled exponential minus one. The reciprocal has norm at most the inverse time at every observation. The improper integral identity remains open.
[GaussianGammaZetaMellinIntegrand](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinIntegrand.lean)

The original real decay and cofinal Binet kernel give a positive rational floor on every bounded time interval, with an explicit observation allowance. This supplies the positive-interval estimate for the Stirling remainder moments.
[GaussianBinetLaplaceRealFloor](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceRealFloor.lean)

The literal same-clock logarithm samples give a quadratic primitive estimate on each positive rational cell. Telescoping compares the original compact logarithm quadrature to the actual endpoint difference with separate mesh and observation errors.
[GaussianRaabeLogPrimitiveCell](Lean/IPRADerivations/Analysis/GaussianRaabeLogPrimitiveCell.lean), [GaussianRaabeLogPrimitiveGrid](Lean/IPRADerivations/Analysis/GaussianRaabeLogPrimitiveGrid.lean)

At a rooted time t=(a/b)^A, the actual Mellin observation for the parameter s is bounded by (b/a)^(A−1)+3·2^-p on the admitted chart for s−1. The exact time factor cancels the reciprocal norm bound.
[GaussianGammaZetaMellinOriginBound](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinOriginBound.lean)

The actual compact quadrature inherits the pointwise rational floor with its physical width. On [1,2] the late samples have real part at least 1/(104·3^(2X)), with explicit dyadic admission.
[GaussianBinetLaplaceCompactRealFloor](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceCompactRealFloor.lean)

The actual unscaled reciprocal is approximated by the finite powers of the inverse of its exact positive exponential sample. On a strip with time at least 1/H the uniform error is bounded by H²/(H+N), before weighting by the original Euler power.
[GaussianGammaZetaMellinGeometric](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinGeometric.lean)

At the actual reciprocal clock, every retained geometric term compares to the original Euler decay evaluated at the positive integer multiple of time. Its inverse retiming cost has an explicit dyadic denominator.
[GaussianGammaZetaMellinDecayRows](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinDecayRows.lean)

The original logarithm observations on equal positive rational charts compare at independent precisions. Multiplication by the common physical endpoint preserves a uniform rate, including the exact grid rescaling.
[GaussianRaabeLogPrimitiveRescale](Lean/IPRADerivations/Analysis/GaussianRaabeLogPrimitiveRescale.lean)

An exact rational t^j factor weights the original cofinal Laplace sample. On the original compact grid [1,2], every late natural moment has the same strict positive floor as the unweighted panel.
[GaussianBinetLaplaceMomentFloor](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceMomentFloor.lean)

Each original right-tag observation is weighted by its exact powered cell width. The finite rooted grid sum is bounded by 4·2^-h as soon as its span in the root coordinate meets the certified dyadic budget.
[GaussianGammaZetaMellinOriginCell](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinOriginCell.lean), [GaussianGammaZetaMellinOriginGrid](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinOriginGrid.lean)

The deviation of the actual unit log-Gamma quadrature from the logarithm primitive has an explicit finite bound under an arbitrary integer shift. The same mesh count and observation clock are used throughout the telescope.
[GaussianRaabeUnitGridShift](Lean/IPRADerivations/Analysis/GaussianRaabeUnitGridShift.lean)

At every actual logarithm observation on a large positive unit interval, the elementary Stirling term compares to a centered affine model with an explicit inverse-argument and dyadic error. This supplies the local estimate for the far-field average.
[GaussianRaabeStirlingCell](Lean/IPRADerivations/Analysis/GaussianRaabeStirlingCell.lean)

An explicit modulus combines the original Laplace time estimate with the exact power t^j. It certifies regularity of the original weighted quadrature on arbitrary admissible compact strips and on [1,2].
[GaussianBinetLaplaceMomentCompact](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceMomentCompact.lean)

The centered left grid has exact mean −1/(2N). Averaging the checked elementary Stirling samples gives the literal endpoint primitive with the explicit inverse-argument error, dyadic error, and a mesh-bias coefficient independent of the mesh.
[GaussianRaabeCenteredMesh](Lean/IPRADerivations/Analysis/GaussianRaabeCenteredMesh.lean), [GaussianRaabeAffineMean](Lean/IPRADerivations/Analysis/GaussianRaabeAffineMean.lean), [GaussianRaabeStirlingMesh](Lean/IPRADerivations/Analysis/GaussianRaabeStirlingMesh.lean)

The exact rational weight commutes with the original horizon comparison. Weighted compact integrals agree whenever both charts cover the same physical panel, including the independently sampled row comparison.
[GaussianBinetLaplaceMomentHorizon](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceMomentHorizon.lean)

At a common admissible horizon, the original weighted quadrature on consecutive strips agrees with the sum of their regular names.
[GaussianBinetLaplaceMomentAdditivity](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceMomentAdditivity.lean)

The original positive-window Mellin observations compare with the finite weighted Euler decay prefix on the same physical tags. A computed common clock controls the decay rows and leaves the exact geometric truncation allowance.
[GaussianGammaZetaMellinDecayPrefix](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinDecayPrefix.lean), [GaussianGammaZetaMellinStrip](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinStrip.lean)

The original real Stirling remainder controls actual common-clock log-Gamma and logarithm observations. Explicit schedules bound the finite shift, elementary and remainder errors after choosing the distant interval and mesh. The right side is the regular name for the logarithm primitive plus the original Stirling constant.
[GaussianRaabeStirlingRemainder](Lean/IPRADerivations/Analysis/GaussianRaabeStirlingRemainder.lean), [GaussianRaabeRightSide](Lean/IPRADerivations/Analysis/GaussianRaabeRightSide.lean), [GaussianRaabeCofinalSchedule](Lean/IPRADerivations/Analysis/GaussianRaabeCofinalSchedule.lean)

The original weighted finite Mellin rectangle can be summed first over time or first over the decay index. The transposed columns retain the actual Euler samples at positive integer multiples of the original time tags.
[GaussianGammaZetaMellinTranspose](Lean/IPRADerivations/Analysis/GaussianGammaZetaMellinTranspose.lean)

The original weighted compact observations have a physical width bound. In the unit time window the bound is the width itself, uniformly in the internal natural moment order.
[GaussianBinetLaplaceMomentWidth](Lean/IPRADerivations/Analysis/GaussianBinetLaplaceMomentWidth.lean)
