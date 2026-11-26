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
| Barnes product | [Head products](Barnes/HeadProducts/), [deflation and zeros](Barnes/Deflation/), [prefactors](Barnes/Prefactors/), [logarithms](Barnes/Logarithms/), and [regular names](Barnes/Names/) |
| Barnes Taylor theory | [First derivatives](Barnes/Taylor/FirstDerivative/), [relative expansions](Barnes/Taylor/RelativeExpansions/), [coefficient buffers and names](Barnes/Taylor/Coefficients/), and [finite and cofinal grids](Barnes/Taylor/Grids/) |
| Gamma | [Poles](Gamma/Poles/), [half-integer values](Gamma/HalfInteger/), [ratio inequalities](Gamma/Ratios/), and [Taylor coefficients](Gamma/Taylor/) |
| Gamma Euler products | [Canonical products](Gamma/EulerProducts/CanonicalProducts/), [Gauss products](Gamma/EulerProducts/Gauss/), and [log Gamma](Gamma/EulerProducts/LogGamma/) |
| Euler integrals | [Compact exhaustion](Euler/CompactExhaustion/), [power scaling](Euler/PowerScaling/), and [vertical bounds](Euler/VerticalBounds/) |
| Euler integrals on the positive axis | [Power charts](Euler/PositiveAxis/PowerCharts/), [sharp rates](Euler/PositiveAxis/SharpRates/), [unit kernels](Euler/PositiveAxis/UnitKernel/), and [unit substitutions](Euler/PositiveAxis/UnitSubstitution/) |
| Polynomials | [Determinants](Polynomials/Determinants/), [finite differences](Polynomials/FiniteDifferences/), and [Horner evaluation](Polynomials/Horner/) |
| Rational arithmetic | [Covers](RationalArithmetic/Covers/), [finite products](RationalArithmetic/FiniteProducts/), and [spans and minors](RationalArithmetic/Spans/) |
| Stirling's formula | Binet's [Bose integral](Stirling/Binet/Bose/), [kernels](Stirling/Binet/Kernel/), and [second formula](Stirling/Binet/SecondFormula/) |

For example, the module `IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupNamedGamma` contains the theorem `LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma.actual_named_Bohr_Mollerup_Gamma_closed`.

The [derivations index](../../../README.md) and [progress ledger](../../../PROGRESS.md) link each reported result to its Lean source.
