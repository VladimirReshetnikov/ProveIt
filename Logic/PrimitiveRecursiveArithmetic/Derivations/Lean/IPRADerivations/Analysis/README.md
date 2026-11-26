# Analysis in iPRA

The Lean modules in this directory construct derivations in the object theory. Their module paths follow the topic directories, and their declarations use the `LeanProofs.IPRA.Analysis` namespace.

| Directory | Contents |
| --- | --- |
| [Barnes](Barnes/), [Beta](Beta/), [Euler](Euler/), [Gamma](Gamma/), [Stirling](Stirling/) | Classical special functions and their constructive evaluators, functional equations, and error bounds. Binet formulas sit under Stirling and Bohr–Mollerup under Gamma. |
| [Exponential](Exponential/), [Logarithm](Logarithm/), [Trigonometry](Trigonometry/) | Elementary transcendental functions, series, and estimates. |
| [Series](Series/), [SpecialFunctions](SpecialFunctions/) | Summation estimates and functions such as Lambert W. |
| [Integration](Integration/), [DifferentialEquations](DifferentialEquations/) | Quadrature, integral constructions, and ODE certificates. |
| [Polynomials](Polynomials/), [LinearAlgebra](LinearAlgebra/) | Coefficient operations, root finding, elimination, determinants, and matrix estimates. |
| [Geometry](Geometry/), [Optimization](Optimization/), [Inequalities](Inequalities/) | Geometric estimates, convexity, and optimization. |
| [RationalArithmetic](RationalArithmetic/), [FiniteOperations](FiniteOperations/) | Rational and Gaussian arithmetic and finite algebraic operations. |
| [Names](Names/), [Observation](Observation/) | Regular names, rate transport, and finite observation certificates. |
| [Quantum](Quantum/) | Constructive quantum identities and estimates. |

## Larger collections

| Collection | Subdirectories |
| --- | --- |
| Barnes product | [Head products](Barnes/HeadProducts/), [deflation and zeros](Barnes/Deflation/), [prefactors](Barnes/Prefactors/), [regular names](Barnes/Names/), [growth](Barnes/Growth/), and [tail control](Barnes/TailControl/) |
| Barnes logarithms | [Finite rows](Barnes/Logarithms/FiniteRows/), [cofinal tails](Barnes/Logarithms/CofinalTails/), and the positive-axis logarithm and its [first](Barnes/Logarithms/PositiveAxis/FirstDerivative/), [second](Barnes/Logarithms/PositiveAxis/SecondDerivative/), and [third](Barnes/Logarithms/PositiveAxis/ThirdDerivative/) derivatives |
| Barnes functional equations | [Unit shift](Barnes/FunctionalEquations/UnitShift/), [duplication](Barnes/FunctionalEquations/Duplication/), [integer values](Barnes/FunctionalEquations/IntegerValues/), [hyperfactorials](Barnes/FunctionalEquations/Hyperfactorial/), [the Glaisher constant](Barnes/FunctionalEquations/Glaisher/), and [Vignéras uniqueness](Barnes/Vigneras/) |
| Barnes Taylor theory | [Centered charts](Barnes/Taylor/CenteredCharts/), [Taylor balls](Barnes/Taylor/TaylorBalls/), [first derivatives](Barnes/Taylor/FirstDerivative/), [relative expansions](Barnes/Taylor/RelativeExpansions/), [coefficients](Barnes/Taylor/Coefficients/), and [grids](Barnes/Taylor/Grids/) including [even](Barnes/Taylor/Grids/EvenGrids/), [mixed](Barnes/Taylor/Grids/MixedGrids/), and [differentiation](Barnes/Taylor/Grids/Differentiation/) |
| Barnes derivatives | First derivatives of [finite factors](Barnes/Taylor/FirstDerivative/FiniteFactors/), [prefactors](Barnes/Taylor/FirstDerivative/Prefactors/), and [tail factors](Barnes/Taylor/FirstDerivative/TailFactors/), with [cofinal estimates](Barnes/Taylor/FirstDerivative/Cofinal/) and [named values](Barnes/Taylor/FirstDerivative/NamedValues/). Relative expansions include [corrected Mercator series](Barnes/Taylor/RelativeExpansions/CorrectedMercator/), [second derivatives](Barnes/Taylor/RelativeExpansions/SecondDerivative/), and [higher orders](Barnes/Taylor/RelativeExpansions/HigherOrders/). |
| Beta | [Compact kernels](Beta/CompactKernels/), [endpoints](Beta/Endpoints/), [Euler products](Beta/EulerProducts/), [partitions](Beta/Partitions/), [primitives](Beta/Primitives/), and [tails](Beta/Tails/) |
| Elementary functions | Exponential [finite series](Exponential/FiniteSeries/) and [names](Exponential/Names/), logarithm [finite series](Logarithm/FiniteSeries/) and [right-half-plane charts](Logarithm/RightHalfPlane/), trigonometric [sine products](Trigonometry/SineProducts/) and [arctangent](Trigonometry/Arctangent/) |
| Sine products | [Bounds](Trigonometry/SineProducts/Bounds/), [argument scaling](Trigonometry/SineProducts/Scaling/), [root representations](Trigonometry/SineProducts/Roots/), and [sample products](Trigonometry/SineProducts/SampleProducts/) |
| Gamma | [Poles](Gamma/Poles/), [negative axis](Gamma/NegativeAxis/), [half-integer values](Gamma/HalfInteger/), [ratio inequalities](Gamma/Ratios/), [functional equations](Gamma/FunctionalEquations/), and [Taylor coefficients](Gamma/Taylor/) |
| Gamma derivatives and zeta | [Digamma](Gamma/Digamma/), [critical points](Gamma/CriticalPoints/), [Dirichlet series](Gamma/Zeta/Dirichlet/), and [Mellin integrals](Gamma/Zeta/Mellin/) |
| Gamma Euler products | [Canonical products](Gamma/EulerProducts/CanonicalProducts/), [Gauss products](Gamma/EulerProducts/Gauss/), [finite heads](Gamma/EulerProducts/FiniteHeads/), and [log Gamma](Gamma/EulerProducts/LogGamma/) |
| Euler integration | [Compact exhaustion](Euler/CompactExhaustion/), [decay](Euler/Integration/Decay/), [incomplete integrals](Euler/Integration/Incomplete/), [integration by parts](Euler/Integration/Parts/), [power scaling](Euler/PowerScaling/), and [vertical bounds](Euler/VerticalBounds/) |
| Euler integrals on the positive axis | [Power charts](Euler/PositiveAxis/PowerCharts/), [sharp rates](Euler/PositiveAxis/SharpRates/), [unit kernels](Euler/PositiveAxis/UnitKernel/), and [unit substitutions](Euler/PositiveAxis/UnitSubstitution/) |
| Euler power charts | [Image grids](Euler/PositiveAxis/PowerCharts/ImageGrids/), [endpoint schedules](Euler/PositiveAxis/PowerCharts/Endpoints/), and [logarithms and rational powers](Euler/PositiveAxis/PowerCharts/Logarithms/) |
| Integration methods | [Compact grids](Integration/CompactGrids/), [moments](Integration/Moments/), [partitions](Integration/Partitions/), and [quadrature](Integration/Quadrature/) |
| Periodic grids | [Signed observations, finite differences, and cubic estimates](FiniteOperations/PeriodicGrids/) |
| Polynomials | [Coefficients](Polynomials/Coefficients/), [determinants](Polynomials/Determinants/), [elimination](Polynomials/Elimination/), [finite differences](Polynomials/FiniteDifferences/), [Horner evaluation](Polynomials/Horner/), and [root finding](Polynomials/RootFinding/) |
| Rational arithmetic | [Covers](RationalArithmetic/Covers/), [finite products](RationalArithmetic/FiniteProducts/), [finite sums](RationalArithmetic/FiniteSums/), [grids](RationalArithmetic/Grids/), [representations](RationalArithmetic/Representations/), and [spans and minors](RationalArithmetic/Spans/) |
| Rational and Gaussian estimates | [Embeddings](RationalArithmetic/Embeddings/), [order bounds](RationalArithmetic/OrderBounds/), [scaling](RationalArithmetic/Scaling/), and [circle parametrization](RationalArithmetic/Complex/Circle/) |
| Inequalities | [Nonnegative arithmetic](Inequalities/NonnegativeArithmetic/), [contraction](Inequalities/Contraction/), [weighted comparison](Inequalities/WeightedComparison/), and [positive radius](Inequalities/PositiveRadius/) |
| Regular names | [Approximation](Names/Approximation/), [differences](Names/Differences/), [finite operations](Names/FiniteOperations/), [rates](Names/Rates/), and [right-half-plane certificates](Names/RightHalfPlane/) |
| Operations on names | [Arithmetic](Names/Arithmetic/), [branch constructions](Names/Branches/), [finite sums](Names/FiniteOperations/Sums/), and [finite products](Names/FiniteOperations/Products/) |
| Stirling's formula | [All-orders expansion](Stirling/AllOrders/), [bounds](Stirling/Bounds/), and Binet's [Bose integral](Stirling/Binet/Bose/), [kernels](Stirling/Binet/Kernel/), [Laplace integrals](Stirling/Binet/Laplace/), [oscillatory integrals](Stirling/Binet/Oscillatory/), and [second formula](Stirling/Binet/SecondFormula/) |
| Binet Bose integral | [Compact integrand](Stirling/Binet/Bose/CompactIntegrand/), [frozen rows](Stirling/Binet/Bose/FrozenRows/), [prefix quadrature](Stirling/Binet/Bose/PrefixQuadrature/), [literal tails](Stirling/Binet/Bose/LiteralTails/), and [improper names](Stirling/Binet/Bose/ImproperNames/) |
| Binet Laplace moments | [Finite rows](Stirling/Binet/Laplace/Moments/FiniteRows/), [positivity](Stirling/Binet/Laplace/Moments/Positivity/), [derivative quotients](Stirling/Binet/Laplace/Moments/DerivativeQuotients/), [Taylor estimates](Stirling/Binet/Laplace/Moments/Taylor/), [improper moments](Stirling/Binet/Laplace/Moments/Improper/), and [named moments](Stirling/Binet/Laplace/Moments/Named/) |
| Binet's second formula | [Decay bounds](Stirling/Binet/SecondFormula/Decay/), [frozen kernels](Stirling/Binet/SecondFormula/FrozenKernels/), and [weighted sine estimates](Stirling/Binet/SecondFormula/WeightedSine/) |
| Binet oscillatory integrals | [Arctangent](Stirling/Binet/Oscillatory/Arctangent/), [fixed horizons](Stirling/Binet/Oscillatory/FixedHorizons/), [rectangular grids](Stirling/Binet/Oscillatory/Rectangles/), [sine kernels](Stirling/Binet/Oscillatory/SineKernels/), and [sine transforms](Stirling/Binet/Oscillatory/SineTransforms/) |

Import a file using its path within the Lean library. For example, `IPRADerivations.Analysis.Gamma.BohrMollerup.Named.GaussianBohrMollerupNamedGamma` contains `LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma.actual_named_Bohr_Mollerup_Gamma_closed`.

The [derivations index](../../../README.md) and [progress ledger](../../../PROGRESS.md) link each reported result to its Lean source.
