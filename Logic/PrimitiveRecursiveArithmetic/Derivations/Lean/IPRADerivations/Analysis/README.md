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

For example, the module `IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupNamedGamma` contains the theorem `LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma.actual_named_Bohr_Mollerup_Gamma_closed`.

The [derivations index](../../../README.md) and [progress ledger](../../../PROGRESS.md) link each reported result to its Lean source.
