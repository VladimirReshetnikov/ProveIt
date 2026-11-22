# Finite observations in constructive arithmetic

Open **report.pdf** for the paper. Its editable source is report.tex with the seven files under sections/ and the two PDF figures under figures/.

The central construction takes a net-equipped rational pseudometric and produces finite nets inside its space of bounded scalar Lipschitz functions. Distances between finite envelope codes are exact. The type construction iterates to spaces of functionals. Other chapters treat continuous model theory, approximate descent, closed-box nerve homotopies and residues at named singularities.

## Verification status

| File | Checked result |
| --- | --- |
| lean/ObjectTransport.lean | A quantifier-transport derivation constructor in ProveIt's embedded iPRA calculus, with explicit object terms and object derivations at leaves |
| lean/FunctionSpace.lean | Exact code metric, unit-interval code carrier, approximation by noisy samples, and optimization-witness transport along nonexpansive retractions |
| lean/Variational.lean | Rational lower bound, optimal feasible approximant and attainment for the quadratic minimax problem |
| lean/Abstract.lean | Composition of correspondences, continuous formula transport, interval–circle obstruction and approximate gluing bound |
| lean/Topology.lean | Intersection arithmetic, common-coordinate mass, normalization, support and weight totals on the two homotopy segments |
| lean/Complex.lean | Gaussian-rational quadrature comparison, the four-side strip boundary identity and regularity of diagonal coefficient names |

The five modules following ObjectTransport check lemmas in Lean's host theory. The full programming of the application proofs into object-level Prf PRAAx derivations remains open. The last chapter and the end of each application give the reification steps and dependencies. The analytic application uses the rational Cauchy/Laurent results of the linked ProveIt packet as human-proved lemmas.

## Reproduce the checks

The tested environment is Lean **4.32.0**, ProveIt [5f3be02388442f16487d2dc5c2529961dd783d2b](https://github.com/VladimirReshetnikov/ProveIt/tree/5f3be02388442f16487d2dc5c2529961dd783d2b) and Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997. Use a ProveIt checkout with its Lake dependencies available. From this bundle run:

    PROVEIT_ROOT=/path/to/ProveIt ./check.sh

The script verifies the imported upstream sources and toolchain files, builds the six modules in a temporary output directory, prints the axioms of selected declarations and runs the four exact-arithmetic examples. Its captured output is in verification/lean.txt. The four Python example scripts can also run independently with Python 3.9+ and its standard library.

To rebuild the paper, run the following twice from this directory.

    pdflatex report.tex

The figures are included. Their optional generators use Python, NumPy and Matplotlib.
