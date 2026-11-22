# From oracle observations to iPRA proofs

Start with **report.pdf**. The editable article begins at **report.tex** and includes all the files in **chapters/**. The figure is supplied as a PDF, so rebuilding the paper does not require Python or Matplotlib.

The paper treats sparse oracle replay, root selection from inexact values, differentiation from dyadic second differences, and probability laws from piecewise-linear expectations. Two applications extend the law construction to metric spaces with quantitative partitions and compute quantiles from a transport name with upper and lower density bounds. Each positive result states the finite evidence it consumes. Counterexamples identify the missing information when a stronger claim fails.

## Verification

The replay used Lean **4.32.0**, ProveIt commit **b2341af5370cd8a43f72ebb2341c0d7d7395b634** and the Mathlib checkout at **81a5d257c8e410db227a6665ed08f64fea08e997**. All four Python examples use exact rational arithmetic and only the standard library. The checked Lean modules and their axiom audits are listed in **verification/replay.txt**. **verification/provider-hashes.json** records the git blob hashes of the ProveIt import closure used by the object proofs. That source closure was rebuilt locally against precompiled Lean and Mathlib dependencies.

Run from the unpacked archive:

```sh
python3 verify.py --examples-only
python3 verify.py --standalone --lean /path/to/lean
python3 verify.py --proveit /path/to/ProveIt
pdflatex report.tex
pdflatex report.tex
```

The third command requires a configured checkout of the indicated repository revision, its Lake dependencies, and its toolchain on the path. It verifies the imported source hashes, builds the necessary Lake target and checks the examples and all Lean modules. The standalone command runs the examples and the four modules that use only the Lean distribution. For an already verified build environment, `--object-env` reads its provider paths from `LEAN_PATH`. The script writes compiled objects to a temporary directory. **SOURCES.md** links to the research packets and primary literature. The optional figure source requires Matplotlib.

## Formal results

| File | What is proved |
| --- | --- |
| lean/Oracle.lean | Finite replay and certified windows, composition of prefix dependence, preservation of an extensionality relation, and a two-query no-window example. |
| lean/Zeros.lean | The rational midpoint computation, fixed-precision endpoint invariant, geometric bracket width, cross-stage Cauchy estimate and scheduled residual. |
| lean/DyadicDetail.lean | Both child/parent slope bounds, sample-error propagation and a sharp square-grid identity in signed integers. |
| lean/LineDual.lean | Discrete summation by parts, upper bound for every feasible potential, explicit attaining potential, and scaled integer certificates. |
| lean/ReplayObject.lean | Variable-length replay inside object iPRA. Agreement at queries made by the first run implies equality of the final states. |
| lean/ZeroObject.lean | A closed seven-variable iPRA sentence for the three disjoint midpoint guards and the corresponding endpoint signs. |
| lean/DyadicObject.lean | A closed seven-variable iPRA sentence for the two child/parent inequalities following from an adjacent-slope bound. |
| lean/PrefixObject.lean | Embedded PR prefix-repair symbol, defining equations, monotonicity, coverage of latest sample, variable-length common upper bound by quantifier-free induction. |

The report gives human proofs of the completed analytic constructions. The remaining work for full deep formalization is specified theorem by theorem in the application sections and in the closing formalization plan. The standard Lean axiom reports for the ProveIt derivation constructors are recorded in the replay. The numerical regressions exercise concrete realizers.

## Exact examples

- `examples/zeros.py` runs all three midpoint branches for polynomial and analytic inputs.
- `examples/dyadic_derivative.py` differentiates rounded samples and checks inherited knots.
- `examples/laws.py` reconstructs a mixture with atoms. It checks the marginal sums, primal cost and dual potential, the predicted mesh and query errors, and 300 triangle inequalities.
- `examples/quantiles.py` composes the law and root algorithms. For the density (1/2+x) a closed prefix-moment formula implements the finite-law ramp query. It compares that formula to direct summation and checks 32 root halvings at each of four target masses.

**SHA256SUMS** lists the hashes of all archive members except itself.
