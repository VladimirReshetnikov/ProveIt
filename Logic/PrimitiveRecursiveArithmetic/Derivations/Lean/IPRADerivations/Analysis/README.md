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
| Barnes product | [Head products](Barnes/HeadProducts/), [deflation and zeros](Barnes/Deflation/), [prefactors](Barnes/Prefactors/), [logarithms](Barnes/Logarithms/), [regular names](Barnes/Names/), and [functional equations](Barnes/FunctionalEquations/) |
| Barnes Taylor theory | [First derivatives](Barnes/Taylor/FirstDerivative/), [relative expansions](Barnes/Taylor/RelativeExpansions/), [coefficient buffers and names](Barnes/Taylor/Coefficients/), and [finite and cofinal grids](Barnes/Taylor/Grids/) |
| Beta | [Compact kernels](Beta/CompactKernels/), [endpoints](Beta/Endpoints/), [Euler products](Beta/EulerProducts/), [partitions](Beta/Partitions/), [primitives](Beta/Primitives/), and [tails](Beta/Tails/) |
| Elementary functions | Exponential [finite series](Exponential/FiniteSeries/) and [names](Exponential/Names/), logarithm [finite series](Logarithm/FiniteSeries/) and [right-half-plane charts](Logarithm/RightHalfPlane/), trigonometric [sine products](Trigonometry/SineProducts/) and [arctangent](Trigonometry/Arctangent/) |
| Gamma | [Poles](Gamma/Poles/), [negative axis](Gamma/NegativeAxis/), [half-integer values](Gamma/HalfInteger/), [ratio inequalities](Gamma/Ratios/), [functional equations](Gamma/FunctionalEquations/), and [Taylor coefficients](Gamma/Taylor/) |
| Gamma derivatives and zeta | [Digamma](Gamma/Digamma/), [critical points](Gamma/CriticalPoints/), [Dirichlet series](Gamma/Zeta/Dirichlet/), and [Mellin integrals](Gamma/Zeta/Mellin/) |
| Gamma Euler products | [Canonical products](Gamma/EulerProducts/CanonicalProducts/), [Gauss products](Gamma/EulerProducts/Gauss/), [finite heads](Gamma/EulerProducts/FiniteHeads/), and [log Gamma](Gamma/EulerProducts/LogGamma/) |
| Euler integration | [Compact exhaustion](Euler/CompactExhaustion/), [decay](Euler/Integration/Decay/), [incomplete integrals](Euler/Integration/Incomplete/), [integration by parts](Euler/Integration/Parts/), [power scaling](Euler/PowerScaling/), and [vertical bounds](Euler/VerticalBounds/) |
| Euler integrals on the positive axis | [Power charts](Euler/PositiveAxis/PowerCharts/), [sharp rates](Euler/PositiveAxis/SharpRates/), [unit kernels](Euler/PositiveAxis/UnitKernel/), and [unit substitutions](Euler/PositiveAxis/UnitSubstitution/) |
| Integration methods | [Compact grids](Integration/CompactGrids/), [moments](Integration/Moments/), [partitions](Integration/Partitions/), and [quadrature](Integration/Quadrature/) |
| Polynomials | [Coefficients](Polynomials/Coefficients/), [determinants](Polynomials/Determinants/), [elimination](Polynomials/Elimination/), [finite differences](Polynomials/FiniteDifferences/), [Horner evaluation](Polynomials/Horner/), and [root finding](Polynomials/RootFinding/) |
| Rational arithmetic | [Covers](RationalArithmetic/Covers/), [finite products](RationalArithmetic/FiniteProducts/), [finite sums](RationalArithmetic/FiniteSums/), [grids](RationalArithmetic/Grids/), [representations](RationalArithmetic/Representations/), and [spans and minors](RationalArithmetic/Spans/) |
| Regular names | [Approximation](Names/Approximation/), [differences](Names/Differences/), [finite operations](Names/FiniteOperations/), [rates](Names/Rates/), and [right-half-plane certificates](Names/RightHalfPlane/) |
| Stirling's formula | [All-orders expansion](Stirling/AllOrders/), [bounds](Stirling/Bounds/), and Binet's [Bose integral](Stirling/Binet/Bose/), [kernels](Stirling/Binet/Kernel/), [Laplace integrals](Stirling/Binet/Laplace/), and [second formula](Stirling/Binet/SecondFormula/) |

Import a file using its path within the Lean library. For example, `IPRADerivations.Analysis.Gamma.BohrMollerup.Named.GaussianBohrMollerupNamedGamma` contains `LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma.actual_named_Bohr_Mollerup_Gamma_closed`.

The [derivations index](../../../README.md) and [progress ledger](../../../PROGRESS.md) link each reported result to its Lean source.
